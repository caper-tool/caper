{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable, DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
module Prover where

import Prelude hiding (sequence,foldl,mapM_,mapM,elem,notElem)
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

data Provers = Provers {
                permissionsProver :: FOF PermissionAtomic String -> IO (Maybe Bool),
                valueProver :: FOF ValueExpression String -> IO (Maybe Bool)
                }

isConsistent :: Provers -> ProverT m (Maybe Bool)
-- Check whether the current set of assumptions are consistent
-- (i.e. False does not follow)
isConsistent = undefined

check :: (MonadIO m, MonadPlus m) => Provers -> CheckerT m a -> ProverT m (a, EvarSubstitution)
-- Check that the assertions follow from the assumptions
-- If so, admit them as assumptions, returning the substitution of evars
-- If not, fail this path
check = undefined

isBound :: (Monad m) => VariableID -> ProverT m Bool
-- Determine if the given variable is bound.
isBound = undefined

data Condition v = PermissionCondition (FOF PermissionAtomic v)
                | ValueCondition (FOF ValueAtomic v)
                | EqualityCondition VariableID v

instance Show v => Show (Condition v) where
        show (PermissionCondition pa) = show pa
        show (ValueCondition va) = show va
        show (EqualityCondition v1 v2) = show v1 ++ " = " ++ show v2

data Assumptions = Assumptions {
        bindings :: TC.TContext VariableID VariableType
        assumptions :: [Condition VariableID]
        }

type ProverT = StateT Assumptions

assume :: Condition VariableID -> ProverT m ()
assume (PermissionCondition pass) = do
                ass <- get
                case bindAll (freeVariables pass) of
                        Nothing -> error "


permissionAssumptions :: Assumptions -> [FOF PermissionAtomic VariableID]
-- Extract the assumptions pertaining to permissions
permissionAssumptions ass = permAss (assumptions ass)
        where
                permAss [] = []
                permAss (PermissionCondition pa : xs) = pa : permAss xs
                permAss (EqualityCondition v1 v2 : xs) = if TC.lookup v1 (bindings ass) == VTPermission then (FOFAtom $ PAEq (PEVar v1) (PEVar v2)) : permAss xs else permAss xs
                permAss (_ : xs) = permAss xs
