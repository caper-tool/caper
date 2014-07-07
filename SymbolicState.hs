{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor #-}
module SymbolicState where

import Prelude hiding (sequence,foldl,foldr,mapM_,mapM,elem,notElem,concat)
import ProverDatatypes
import Prover
import Data.Map (Map)
import qualified Data.Map as Map
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet
import Control.Lens
import Control.Monad.State hiding (mapM_,mapM,msum)
import Control.Monad.RWS hiding (mapM_,mapM,msum)
import Data.Foldable
import Data.List (intersperse)

import Parser.AST


-- default (ValueExpression VariableID, Integer, Double)


-- Predicate names are either Strings or the special 
-- cases for heap cells: single cell or multiple (uninitialised) cells
data PredicateName = PName String | PCell | PCells deriving (Eq, Ord)
instance Show PredicateName where
        show (PName s) = s
        show PCell = "#cell"
        show PCells = "#cells"

-- A (default) map from predicate names to the list of
-- types of the predicate parameters.  Here, we'll just
-- have a mapping for PCell
predicateTypes :: Map PredicateName [VariableType]
predicateTypes = Map.fromList [(PCell, [VTValue, VTValue]), -- A #cell has two value parameters
                        (PCells, [VTValue, VTValue])    -- A #cells has two value parameters (start and length)
                        ]


-- PVarBindings map program variables (modelled a Strings) to
-- expressions
type PVarBindings = Map String (Expr VariableID)

-- Predicates are maps from predicate names to multisets of
-- lists of parameters.  That is, for each predicate name
-- there's a bag of the parameters that we have copies of the
-- predicate for.  (Possibly want to use a list or something else
-- instead of MultiSet?)
type Predicates = Map PredicateName (MultiSet [Expr VariableID])

predicateLookup :: PredicateName -> Predicates -> MultiSet [Expr VariableID]
predicateLookup = Map.findWithDefault MultiSet.empty

type Predicate = (PredicateName, [Expr VariableID])

toPredicateList :: Predicates -> [Predicate]
toPredicateList = Map.foldWithKey (\key val rest -> map ((,) key) (MultiSet.toList val) ++ rest) []

showPredicate :: Predicate -> String
showPredicate (PCell, [x, y]) = show x ++ " |-> " ++ show y
showPredicate (PCells, [x, y]) = show x ++ " |-> #cells(" ++ show y ++ ")"
showPredicate (PName s, l) = show s ++ show l

-- Symbolic States!
data SymbState p = SymbState {
        _proverState :: p,
        _ssProgVars :: PVarBindings,
        _ssPreds :: Predicates
        } deriving (Functor)
makeLenses ''SymbState

emptySymbState :: SymbState Assumptions
emptySymbState = SymbState emptyAssumptions Map.empty Map.empty

showPVarBindings :: PVarBindings -> String
showPVarBindings vs = Map.foldWithKey (\pv var s-> (pv ++ " := " ++ show var ++ "\n" ++ s)) "" vs

instance (Show p) => Show (SymbState p) where
        show (SymbState p vs preds) = "Pure facts:" ++ show p ++ "\nProgram variables:\n" ++ showPVarBindings vs ++ "Heap:\n" ++ (concat . intersperse "\n" . map showPredicate . toPredicateList) preds


instance AssumptionLenses p => AssumptionLenses (SymbState p) where
        theAssumptions = proverState . theAssumptions

instance AssertionLenses p => AssertionLenses (SymbState p) where
        theAssertions = proverState . theAssertions

class AssumptionLenses s => SymbStateLenses s where
        progVars :: Simple Lens s PVarBindings
        preds :: Simple Lens s Predicates

instance AssumptionLenses p => SymbStateLenses (SymbState p) where
        progVars = ssProgVars
        preds = ssPreds

emptySymbStateWithVars :: [String] -> SymbState Assumptions
emptySymbStateWithVars vs = execState (do
                bindVarsAs (map VIDNamed vs) VTValue
                ssProgVars .= Map.fromList [(x, var (VIDNamed x)) | x <- vs]) emptySymbState


-- Symbolic state monad transformer
type MSState r = RWST r () (SymbState Assumptions)


{-- Convert a ProverT to an MSState
proverToSState :: (Monad m) => ProverT m a -> MSState m a
proverToSState pt = do
                pfs <- use pureFacts
                (r, pfs') <- lift $ runStateT pt pfs
                pureFacts .= pfs'
                return r
--}


-- Add a pure assumption
--syAssume :: (Monad m) => Condition VariableID -> MSState m ()
--syAssume = proverToSState . assume


validatePredicate :: (MonadState s m, SymbStateLenses s) => Predicate -> m ()
-- Check that a predicate has the correct number and type of parameters
validatePredicate (n, exprs) = chkTypes exprs
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
predicateAssumptions (PCells, [e1, e2]) _ = [(toCondition $ VALt (VEConst 0) e1'),  (toCondition $ VALt (VEConst 0) e2')]
        where
                e1' = toValueExpr e1
                e2' = toValueExpr e2
predicateAssumptions _ _ = []

generatePredicateAssumptions :: (MonadState s m, SymbStateLenses s) => Predicate -> m ()
generatePredicateAssumptions p = do
                                ps <- use preds
                                mapM_ assume (predicateAssumptions p ps)

insertPredicate :: Predicate -> Predicates -> Predicates
insertPredicate (n, es) = Map.insertWith (flip MultiSet.union) n (MultiSet.singleton es)

addPredicate :: (MonadState s m, SymbStateLenses s) => Predicate -> m ()
addPredicate p = preds %= (insertPredicate p)
                
producePredicate :: (MonadState s m, SymbStateLenses s) => Predicate -> m ()
-- Check that a predicate is appropriately typed,
-- generate any pure assumptions from it, and
-- add it to the symbolic state
producePredicate p = do
                validatePredicate p
                generatePredicateAssumptions p
                addPredicate p


takingEachPredInstance :: (MonadPlus m, MonadState s m, SymbStateLenses s) => PredicateName -> m [Expr VariableID]
-- Given a predicate name, will branch on each different
-- instance of the predicate, removing it (one copy) from the
-- predicates and returning the instantiation.
takingEachPredInstance pname = do
                prds <- use preds
                p <- msum $ map return (MultiSet.distinctElems (predicateLookup pname prds))
                preds %= Map.adjust (MultiSet.delete p) pname
                return p

-- Deal with having assertions
type MSCheck r = RWST r () (SymbState Assertions)

wrapStateT :: (Monad m) => (t -> s) -> (s -> t) -> StateT s m a -> StateT t m a
wrapStateT init fin op = StateT $ \s0 -> do
                        (r, t1) <- runStateT op (init s0)
                        return (r, fin t1)

wrapRWST :: (Monad m) => (t -> s) -> (s -> t) -> RWST r w s m a -> RWST r w t m a
wrapRWST init fin op = RWST $ \rd s0 -> do
                        (r, t1, w) <- runRWST op rd (init s0)
                        return (r, fin t1, w)


admitChecks :: (Monad m) => MSCheck r m a -> MSState r m a
-- Admit the assumptions as assertions
admitChecks = wrapRWST (fmap emptyAssertions) (fmap admitAssertions)



check :: (MonadIO m, MonadPlus m, Provers p) => MSCheck p m a -> MSState p m a
check c = admitChecks $ do
                ps <- ask
                r <- c
                justCheck ps
                return r


consumePred :: (Monad m, MonadPlus m) => Predicate -> MSCheck r m ()
consumePred (PCell, [x, y]) = (do
                [e1,e2] <- takingEachPredInstance PCell
                assertEqual x e1
                assertEqual y e2) `mplus`
        (do
                [e1,e2] <- takingEachPredInstance PCells
                assertTrue $ e1 $<=$ x
                assertTrue $ x $<$ e1 $+$ e2
                yval <- newAvar "unk"
                assertEqual y (var yval)
                (assertEqual e1 x `mplus`
                    (do
                        addPredicate (PCells, [e1, toExpr (x $-$ e1)])
                        assertTrue $ (e1 $<$ x)))
                (assertEqual (e1 $+$ e2) (x $+$ VEConst 1) `mplus`
                    (do
                        addPredicate (PCells, [toExpr (x $+$ VEConst 1), toExpr (e1 $+$ e2 $-$ x $-$ VEConst 1)])
                        assertTrue $ (x $+$ VEConst 1) $<$ (e1 $+$ e2))))
                -- add justCheck to fail faster?




consumePredicate :: (Monad m, MonadPlus m) => Predicate -> MSCheck r m ()
consumePredicate p = do
                validatePredicate p
                consumePred p



aexprToExpr :: (MonadState s m, SymbStateLenses s) => AExpr -> m (Expr VariableID)
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
symExLocalAssign :: (Monad m, MonadPlus m, Provers p) => String -> AExpr -> MSState p m ()
symExLocalAssign target expr = do
                newval <- aexprToExpr expr
                progVars %= Map.insert target newval

symExAllocate :: (MonadIO m, MonadPlus m, Provers p) => String -> AExpr -> MSState p m ()
symExAllocate target lenExpr = do
                lenval <- aexprToExpr lenExpr
                check $ do
                        -- Check that the length is positive
                        assertTrue $ VEConst 0 $<$ lenval
                loc <- newAvar target
                producePredicate (PCells, [var loc, lenval])
                progVars %= Map.insert target (var loc)

symExWrite :: (MonadIO m, MonadPlus m, Provers p) => AExpr -> AExpr -> MSState p m ()
symExWrite target expr = do
                loc <- aexprToExpr target
                check $ do
                        oldval <- newEvar "val"
                        consumePredicate (PCell, [loc, var oldval])
                newval <- aexprToExpr expr
                addPredicate (PCell, [loc, newval])

symExRead :: (MonadIO m, MonadPlus m, Provers p) => String -> AExpr -> MSState p m ()
symExRead target eloc = do
                loc <- aexprToExpr eloc
                oldval <- check $ do
                        oldval <- newEvar target
                        consumePredicate (PCell, [loc, var oldval])
                        return oldval
                addPredicate (PCell, [loc, var oldval])
                progVars %= Map.insert target (var oldval)

                
                
--}
