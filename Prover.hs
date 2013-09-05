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


isConsistent :: Provers -> ProverT m (Maybe Bool)
-- Check whether the current set of assumptions are consistent
-- (i.e. False does not follow)
isConsistent = undefined

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
                        b0 <- gets _bindings
                        bs <- runEMT $ TC.bindAll s vt b0 `catch` (\(e :: TypeUnificationException VariableID VariableType) -> error (show e))
                        modify $ bindings .~ bs


declareVars :: (Monad m, Foldable f) => f VariableID -> ProverT m ()
declareVars s = modify $ over bindings (TC.declareAll s)

addAssumption :: (Monad m) => Condition VariableID -> ProverT m ()
addAssumption c = modify $ over assumptions (c :)

assume :: Monad m => Condition VariableID -> ProverT m ()
assume c@(PermissionCondition pass) = do
                        bindVarsAs (freeVariables c) VTPermission
                        addAssumption c
assume c@(ValueCondition cass) = do
                        bindVarsAs (freeVariables c) VTValue
                        addAssumption c
assume c@(EqualityCondition _ _) = do
                        declareVars (freeVariables c)
                        addAssumption c




permissionAssumptions :: Assumptions -> [FOF PermissionAtomic VariableID]
-- Extract the assumptions pertaining to permissions
permissionAssumptions ass = permAss (_assumptions ass)
        where
                permAss [] = []
                permAss (PermissionCondition pa : xs) = pa : permAss xs
                permAss (EqualityCondition v1 v2 : xs) = if TC.lookup v1 (_bindings ass) == TC.JustType VTPermission then (FOFAtom $ PAEq (PEVar v1) (PEVar v2)) : permAss xs else permAss xs
                permAss (_ : xs) = permAss xs
