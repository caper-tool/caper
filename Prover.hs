{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
module Prover where

import Prelude hiding (sequence,foldl,foldr,mapM_,mapM,elem,notElem)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.State hiding (mapM_,mapM)
import Control.Monad.Trans.Maybe
import PermissionsInterface
import Permissions
import Data.Maybe
import Data.Foldable
import Data.Traversable
import Data.Typeable
import Control.Monad hiding (mapM_,mapM)
import ProverDatatypes
import ValueProver
import qualified TypingContext as TC
import FirstOrder
import Exceptions
import Control.Lens


type ProverT = StateT Assumptions
-- Invariant: All variables occuring free in assumptions MUST be bound in bindings


--check :: (MonadIO m, MonadPlus m) => Provers -> CheckerT m a -> ProverT m (a, EvarSubstitution)
-- Check that the assertions follow from the assumptions
-- If so, admit them as assumptions, returning the substitution of evars
-- If not, fail this path
check = undefined

isBound :: (Monad m) => VariableID -> ProverT m Bool
-- Determine if the given variable is bound.
isBound = undefined

data Condition v = PermissionCondition (FOF PermissionAtomic v)
                | ValueCondition (FOF ValueAtomic v)
                | EqualityCondition v v

instance FreeVariables Condition where
        foldrFree f x (PermissionCondition fof) = foldrFree f x fof
        foldrFree f x (ValueCondition fof) = foldrFree f x fof
        foldrFree f x (EqualityCondition a b) = foldr f x [a,b]
        

instance Show v => Show (Condition v) where
        show (PermissionCondition pa) = show pa
        show (ValueCondition va) = show va
        show (EqualityCondition v1 v2) = show v1 ++ " = " ++ show v2

data Assumptions = Assumptions {
        _bindings :: TC.TContext VariableID VariableType,
        _assumptions :: [Condition VariableID]
        }
makeLenses ''Assumptions


bindVarsAs :: (Monad m, Foldable f) => f VariableID -> VariableType -> ProverT m ()
bindVarsAs s vt = do
                        b0 <- use bindings
                        bs <- runEMT $ TC.bindAll s vt b0 `catch` (\(e :: TypeUnificationException VariableID VariableType) -> error (show e))
                        bindings .= bs

unifyEqVars :: (Monad m) => VariableID -> VariableID -> ProverT m ()
unifyEqVars v1 v2 = do
                        b0 <- use bindings
                        bs <- runEMT $ TC.unify v1 v2 b0 `catch` (\(e :: TypeUnificationException VariableID VariableType) -> error (show e))
                        bindings .= bs

declareVars :: (Monad m, Foldable f) => f VariableID -> ProverT m ()
declareVars s = bindings %= TC.declareAll s

-- Only use internally
addAssumption :: (Monad m) => Condition VariableID -> ProverT m ()
addAssumption c = assumptions %= (c :)

assume :: Monad m => Condition VariableID -> ProverT m ()
assume c@(PermissionCondition pass) = do
                        bindVarsAs (freeVariables c) VTPermission
                        addAssumption c
assume c@(ValueCondition cass) = do
                        bindVarsAs (freeVariables c) VTValue
                        addAssumption c
assume c@(EqualityCondition v1 v2) = do
                        unifyEqVars v1 v2
                        addAssumption c




permissionAssumptions :: Assumptions -> [FOF PermissionAtomic VariableID]
-- Extract the assumptions pertaining to permissions
permissionAssumptions ass = permAss (_assumptions ass)
        where
                permAss [] = []
                permAss (PermissionCondition pa : xs) = pa : permAss xs
                permAss (EqualityCondition v1 v2 : xs) = if TC.lookup v1 (_bindings ass) == TC.JustType VTPermission then (FOFAtom $ PAEq (PEVar v1) (PEVar v2)) : permAss xs else permAss xs
                permAss (_ : xs) = permAss xs

permissionVariables :: Assumptions -> [VariableID]
-- Return a list of the permission variables
permissionVariables = Map.keys . Map.filter (== Just VTPermission) . TC.toMap . _bindings

valueAssumptions :: Assumptions -> [FOF ValueAtomic VariableID]
-- Extract the assumptions pertaining to values (integers)
-- Equality assumptions where the variable type is indeterminate are treated as value assumptions
valueAssumptions ass = valueAss (_assumptions ass)
        where
                valueAss [] = []
                valueAss (EqualityCondition v1 v2 : xs) =
                        if let t = TC.lookup v1 (ass ^. bindings) in t == TC.JustType VTValue || t == TC.Undetermined then 
                                (FOFAtom $ VAEq (var v1) (var v2)) : valueAss xs
                        else valueAss xs
                valueAss (ValueCondition cass : xs) = cass : valueAss xs
                valueAss (_ : xs) = valueAss xs

valueVariables :: Assumptions -> [VariableID]
-- Return a list of value variables; variables with no other type are treated as value variables
valueVariables = Map.keys . Map.filter (\x -> (x == Just VTValue) || (x == Nothing)) . TC.toMap . _bindings

checkConsistency :: (Functor a, Foldable a) => (FOF a String -> IO (Maybe Bool)) -> [VariableID] -> [FOF a VariableID] -> IO (Maybe Bool)
-- Given a first-order prover, check whether a list of assertions (with free variables from a given list) is consistent.
-- Consistent if the formula ¬(E) x1, ..., xn . P1 /\ ... /\ Pm /\ True is invalid. 
checkConsistency p vars asss = do
                        rp <- p $ FOFNot $ fmap vidToString $ foldr FOFExists (foldr FOFAnd FOFTrue asss) vars
                        return $ fmap not rp

isConsistent :: (MonadIO m) => Provers -> ProverT m (Maybe Bool)
-- Check whether the current set of assumptions are consistent
-- (i.e. False does not follow)
isConsistent ps = get >>= ic
        where
                ic ass = liftIO $ do
                        rp <- checkConsistency (permissionsProver ps) (permissionVariables ass) (permissionAssumptions ass)
                        if rp == Just False then return $ Just False
                        else do
                                rv <- checkConsistency (valueProver ps) (valueVariables ass) (valueAssumptions ass)
                                return $ case (rp, rv) of
                                        (_, Just False) -> Just False
                                        (Just True, Just True) -> Just True
                                        _ -> Nothing

