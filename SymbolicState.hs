{-# LANGUAGE TemplateHaskell #-}
module SymbolicState where

import Prelude hiding (sequence,foldl,foldr,mapM_,mapM,elem,notElem)
import ProverDatatypes
import Prover
import Data.Map (Map)
import qualified Data.Map as Map
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet
import Control.Lens
import Control.Monad.State hiding (mapM_,mapM)
import Data.Foldable

import AST


-- Predicate names are either Strings or the special 
-- cases for heap cells: single cell or multiple (uninitialised) cells
data PredicateName = PName String | PCell | PCells deriving (Eq, Ord)
instance Show PredicateName where
        show (PName s) = s
        show PCell = "#cell"
        show PCell = "#cells"

-- A (default) map from predicate names to the list of
-- types of the predicate parameters.  Here, we'll just
-- have a mapping for PCell
predicateTypes :: Map PredicateName [VariableType]
predicateTypes = Map.fromList [(PCell, [VTValue, VTValue])] -- A #cell has two value parameters


-- PVarBindings map program variables (modelled a Strings) to
-- expressions
type PVarBindings = Map String (Expr VariableID)

-- Predicates are maps from predicate names to multisets of
-- lists of parameters.  That is, for each predicate name
-- there's a bag of the parameters that we have copies of the
-- predicate for.  (Possibly want to use a list or something else
-- instead of MultiSet?)
type Predicates = Map PredicateName (MultiSet [Expr VariableID])

type Predicate = (PredicateName, [Expr VariableID])

-- Symbolic States!
data SymbState = SymbState {
        _pureFacts :: Assumptions,
        _progVars :: PVarBindings,
        _preds :: Predicates
        }
makeLenses ''SymbState

-- Symbolic state monad transformer
type MSState = StateT SymbState

-- Convert a ProverT to an MSState
proverToSState :: (Monad m) => ProverT m a -> MSState m a
proverToSState pt = do
                pfs <- use pureFacts
                (r, pfs') <- lift $ runStateT pt pfs
                pureFacts .= pfs'
                return r

-- Add a pure assumption
syAssume :: (Monad m) => Condition VariableID -> MSState m ()
syAssume = proverToSState . assume


validatePredicate :: Monad m => Predicate -> MSState m ()
-- Check that a predicate has the correct number and type of parameters
validatePredicate (n, exprs) = proverToSState $ chkTypes exprs
        (Map.findWithDefault (error $ "The predicate name '" ++ show n ++ "' is not defined.") n predicateTypes)
        where
                chkTypes [] [] = return ()
                chkTypes (e : es) (t : ts) = checkExpressionAtType e t >> chkTypes es ts
                chkTypes (_ : _) [] = error $ "The predicate '" ++ show n ++ "' is used with too many arguments."
                chkTypes [] (_ : _) = error $ "The predicate '" ++ show n ++ "' is used with too few arguments."

predicateAssumptions :: Predicate -> Predicates -> [Condition VariableID]
predicateAssumptions (PCell, e1 : _) preds = (toCondition $ VALt (VEConst 0) e0) :
                foldMap genCond (Map.findWithDefault MultiSet.empty PCell preds)
        where
                genCond (e1' : _) = [negativeCondition $ VAEq (toValueExpr e1') e0]
                e0 = toValueExpr e1
predicateAssumptions (PCells, [e1, e2]) _ = [(toCondition $ VALt (VEConst 0) e1'),  (toCondition $ VALt (VEConst -1) e2')]
        where
                e1' = toValueExpr e1
                e2' = toValueExpr e2
predicateAssumptions _ _ = []

generatePredicateAssumptions :: Monad m => Predicate -> MSState m ()
generatePredicateAssumptions p = do
                                ps <- use preds
                                mapM_ syAssume (predicateAssumptions p ps)

insertPredicate :: Predicate -> Predicates -> Predicates
insertPredicate (n, es) = Map.insertWith (flip MultiSet.union) n (MultiSet.singleton es)

addPredicate :: Monad m => Predicate -> MSState m ()
addPredicate p = preds %= (insertPredicate p)
                
producePredicate :: Monad m => Predicate -> MSState m ()
-- Check that a predicate is appropriately typed,
-- generate any pure assumptions from it, and
-- add it to the symbolic state
producePredicate p = do
                validatePredicate p
                generatePredicateAssumptions p
                addPredicate p

aexprToExpr :: Monad m => AExpr -> MSState m (Expr VariableID)
-- Generate an expression that represents the
-- value of an arithmetic expression in the current
-- symbolic state
-- Requires: symbolic state contains mappings for all program variables in the expression
-- TODO: If expression evaluation can cause a fault, we ought to assert that the fault cannot occur; division is thus not implemented yet
aexprToExpr (VarAExpr s x) = do
                        bnds <- use progVars
                        return $! Map.findWithDefault (error $ show s ++ " The variable '" ++ x ++ "' has no symbolic value.") x bnds
aexprToExpr (ConstAExpr s n) = return $! integerExpr n
aexprToExpr (NegAExpr s e) = do
                        e' <- aexprToExpr e
                        return $! toExpr $ (VEMinus (VEConst 0) (toValueExpr e'))
aexprToExpr (BinaryAExpr s op e1 e2) = do
                        e1' <- aexprToExpr e1
                        e2' <- aexprToExpr e2
                        return $! toExpr $ (opi op) (toValueExpr e1') (toValueExpr e2')
                where
                        opi Add = VEPlus
                        opi Subtract = VEMinus
                        opi Multiply = VETimes
                        opi Divide = error $ show s ++ " The division operator is not yet supported."



--------------------------------------------
-- Symbolic execution of basic statements --
--------------------------------------------
symExLocalAssign :: (Monad m, MonadPlus m) => String -> AExpr -> MSState m ()
symExLocalAssign target expr = do
                newval <- aexprToExpr expr
                progVars %= Map.insert target newval

symExAllocate :: (Monad m, MonadPlus m) => String -> AExpr -> MSState m ()
symExAllocate target lenExpr = do
                -- Check that the length is positive
                

