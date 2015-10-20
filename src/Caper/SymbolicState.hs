{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor, FlexibleContexts, MultiParamTypeClasses #-}
module Caper.SymbolicState where

import Prelude hiding (sequence,foldl,foldr,mapM_,mapM,elem,notElem,concat,concatMap)
-- import Data.Map (Map)
import qualified Data.Map as Map
-- import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet
import Control.Lens hiding (op)
import Control.Monad.State hiding (mapM_,mapM,msum,forM_)
import Control.Monad.RWS hiding (mapM_,mapM,msum,forM_)
import Data.Foldable
import Data.List (intersperse)
import Data.Traversable
import Data.Maybe

import Caper.Utils.Choice
import Caper.Utils.NondetClasses
import Caper.Logger
import Caper.ProverDatatypes
import Caper.Prover
import qualified Caper.Utils.AliasingMap as AliasMap
import Caper.Parser.AST.Code
import Caper.Regions
import Caper.RegionTypes
import Caper.Exceptions
import Caper.Predicates

-- default (ValueExpression VariableID, Integer, Double)


-- Symbolic States!
data SymbState p = SymbState {
        _proverState :: p,
        _ssProgVars :: PVarBindings,
        _ssLogicalVars :: LVarBindings,
        _ssPreds :: Predicates,
        _ssRegions :: Regions -- AliasMap.AliasMap VariableID Region
        } deriving (Functor)
makeLenses ''SymbState

emptySymbState :: SymbState Assumptions
emptySymbState = SymbState emptyAssumptions Map.empty emptyLVars Map.empty emptyRegions

showPVarBindings :: PVarBindings -> String
showPVarBindings = Map.foldWithKey showBinding ""
        where
                showBinding pv vr s = pv ++ " := " ++ show vr ++ "\n" ++ s

instance (Show p) => Show (SymbState p) where
        show (SymbState p vs lvs prds regs) = "Pure facts:\n" ++ show p 
                ++ "\nProgram variables:\n" ++ showPVarBindings vs 
                ++ "Heap:\n" ++ 
                (concat . intersperse "\n" . 
                        map showPredicate . toPredicateList) prds


instance AssumptionLenses p => AssumptionLenses (SymbState p) where
        theAssumptions = proverState . theAssumptions

instance AssertionLenses p => AssertionLenses (SymbState p) where
        theAssertions = proverState . theAssertions

class AssumptionLenses s => SymbStateLenses s where
        progVars :: Simple Lens s PVarBindings
        logicalVars :: Simple Lens s LVarBindings
        preds :: Simple Lens s Predicates

instance AssumptionLenses p => SymbStateLenses (SymbState p) where
        progVars = ssProgVars
        logicalVars = ssLogicalVars
        preds = ssPreds

instance RegionLenses (SymbState p) where
        theRegions = ssRegions

instance SymbStateLenses s => SymbStateLenses (WithAssertions s) where
        progVars = withAssrBase . progVars
        logicalVars = withAssrBase . logicalVars
        preds = withAssrBase . preds

emptySymbStateWithVars :: [String] -> SymbState Assumptions
emptySymbStateWithVars vs = flip execState emptySymbState $ do
                bindVarsAs (map VIDNamed vs) VTValue
                ssProgVars .= Map.fromList [(x, var (VIDNamed x)) | x <- vs]
                ssLogicalVars .= Map.fromList [(x, VIDNamed x) | x <- vs]

newtype InformedRegion = InformedRegion (Region, Maybe RegionType)

instance Show InformedRegion where
        show (InformedRegion (Region drty (Just (RegionInstance _ params)) s gd, Just rt)) =
                rtRegionTypeName rt ++ "("
                        ++ concatMap ((++ ",") . show) params
                        ++ maybe "_" show s
                        ++ ")" ++ (if drty then "*" else "") ++ ": " ++ show gd ++ "\n"
        show (InformedRegion (Region _ _ s gd, _)) = "?(" ++ maybe "_" show s ++ "): " ++ show gd ++ "\n"

showSymbState :: (MonadState (SymbState p) m, Show p, MonadReader r m, RTCGetter r) => m String
showSymbState = do
                stte <- get
                iregs <- mapM inform (stte ^. regions)
                return $ show stte ++ "\nRegions:\n" ++ show iregs
        where
                inform reg = case regTypeInstance reg of
                        (Just (RegionInstance rtid _)) -> do
                                        rt <- lookupRType rtid
                                        return $ InformedRegion (reg, Just rt)
                        _ -> return $ InformedRegion (reg, Nothing)

printSymbState :: (MonadState (SymbState p) m, Show p, MonadReader r m, RTCGetter r, MonadIO m) => m ()
printSymbState = showSymbState >>= liftIO . putStrLn

validatePredicate :: (MonadState s m, SymbStateLenses s) => Predicate -> m ()
-- ^Check that a predicate has the correct number and type of parameters.
validatePredicate (n, exprs) = chkTypes exprs
        (Map.findWithDefault (error $ "The predicate name '" ++ show n ++ "' is not defined.") n predicateTypes)
        where
                chkTypes [] [] = return ()
                chkTypes (e : es) (t : ts) = checkExpressionAtType e t >> chkTypes es ts
                chkTypes (_ : _) [] = error $ "The predicate '" ++ show n ++ "' is used with too many arguments."
                chkTypes [] (_ : _) = error $ "The predicate '" ++ show n ++ "' is used with too few arguments."



predicateAssumptions :: Predicate -> Predicates -> [Condition VariableID]
predicateAssumptions (PCell, e1 : _) prds = toCondition (VALt (VEConst 0) e0) :
                foldMap genCond (Map.findWithDefault MultiSet.empty PCell prds)
        where
                genCond (e1' : _) = [negativeCondition $ VAEq (toValueExpr e1') e0]
                e0 = toValueExpr e1
predicateAssumptions (PCells, [e1, e2]) _ = [toCondition (VALt (VEConst 0) e1'),  toCondition (VALt (VEConst 0) e2')]
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
addPredicate p = preds %= insertPredicate p
                
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
                p <- chooseFrom (MultiSet.distinctElems (predicateLookup pname prds))
                preds %= Map.adjust (MultiSet.delete p) pname
                return p

{-

wrapStateT :: (Monad m) => (t -> s) -> (s -> t) -> StateT s m a -> StateT t m a
wrapStateT initial fin op = StateT $ \s0 -> do
                        (r, t1) <- runStateT op (initial s0)
                        return (r, fin t1)

wrapRWST :: (Monad m) => (t -> s) -> (s -> t) -> RWST r w s m a -> RWST r w t m a
wrapRWST initial fin op = RWST $ \rd s0 -> do
                        (r, t1, w) <- runRWST op rd (initial s0)
                        return (r, fin t1, w)
-}

-- |Admit the assumptions as assertions
admitChecks :: (MonadState s m, AssumptionLenses s) => StateT (WithAssertions s) m a -> m a
admitChecks o = do
                initial <- get
                (r, s') <- runStateT o (emptyWithAssertions initial)
                put $ (s' & theAssumptions .~ admitAssertions s') ^. withAssrBase
                return r

check :: (AssumptionLenses s, MonadLogger m, Provers p, MonadReader p m,
            MonadIO m, MonadState s m, MonadPlus m) =>
           StateT (WithAssertions s) m a -> m a
check c = admitChecks $ do
                r <- c
                justCheck
                return r

-- |Consumes a predicate.  Does not check that the predicate is well-formed.
-- 
-- FIXME: Case handling for PCells and other predicates
consumePred :: (Monad m, MonadPlus m, MonadState s m, MonadLogger m,
        AssertionLenses s, SymbStateLenses s) => Predicate -> m ()
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
                assertEqual e1 x `mplus`
                    (do
                        addPredicate (PCells, [e1, toExpr (x $-$ e1)])
                        assertTrue $ e1 $<$ x)
                assertEqual (e1 $+$ e2) (x $+$ VEConst 1) `mplus`
                    (do
                        addPredicate (PCells, [toExpr (x $+$ VEConst 1), toExpr (e1 $+$ e2 $-$ x $-$ VEConst 1)])
                        assertTrue $ (x $+$ VEConst 1) $<$ (e1 $+$ e2)))
                -- add justCheck to fail faster?


-- |Consumes a predicate, after checking that it is well-formed.
--
-- TODO: This should not be used as-is; it should be changed so that validation
-- failures raise exceptions and some kind of context is used for resolving the
-- number/type information for validation.
--
-- TD-Y: I'm going to use this stuff as is; at some point the front-end will be
-- redesigned to simplify the parser and provide an input validation/type-
-- checking phase.
{-consumePredicate :: (Monad m, MonadPlus m, MonadLogger m) =>
        Predicate -> MSCheck r m ()
        -}
consumePredicate :: 
                      (SymbStateLenses s, AssertionLenses s, MonadLogger m,
                       MonadState s m, MonadPlus m) =>
                      Predicate -> m ()
consumePredicate p = do
                validatePredicate p
                consumePred p



aexprToVExpr :: (MonadState s m, SymbStateLenses s, MonadLogger m, MonadRaise m) => AExpr -> m (ValueExpression VariableID)
-- | Generate an expression that represents the
-- value of an arithmetic expression in the current
-- symbolic state
-- Requires: symbolic state contains mappings for all program variables in the expression
-- TODO: If expression evaluation can cause a fault, we ought to assert that the fault cannot occur; division is thus not implemented yet
aexprToVExpr (VarAExpr s x) = do
                        bnds <- use progVars
                        case Map.lookup x bnds of
                            Nothing -> do
                                addSPContext s $ logEvent $ WarnUninitialisedVariable x
                                xv <- newAvar x
                                progVars %= Map.insert x (var xv)  
                                return $ var xv
                            Just xv -> return xv
aexprToVExpr (ConstAExpr s n) = return $! VEConst n
aexprToVExpr (NegAExpr s e) = do
                        e' <- aexprToVExpr e
                        return $! VEMinus (VEConst 0) (toValueExpr e')
aexprToVExpr (BinaryAExpr s op e1 e2) = do
                        e1' <- aexprToVExpr e1
                        e2' <- aexprToVExpr e2
                        theOp <- opi op
                        return $! theOp (toValueExpr e1') (toValueExpr e2')
                where
                        opi Add = return VEPlus
                        opi Subtract = return VEMinus
                        opi Multiply = return VETimes
                        opi Divide = raise $ SyntaxNotImplemented "division (/)"

aexprToExpr :: (MonadState s m, SymbStateLenses s, MonadLogger m, MonadRaise m) => AExpr -> m (Expr VariableID)
aexprToExpr ae = liftM toExpr (aexprToVExpr ae)


bexprToValueCondition :: (MonadState s m, SymbStateLenses s, MonadLogger m, MonadRaise m) =>
            BExpr -> m (FOF ValueAtomic VariableID)
bexprToValueCondition (ConstBExpr _ b) = return $ if b then FOFTrue else FOFFalse
bexprToValueCondition (NotBExpr _ e) = liftM FOFNot (bexprToValueCondition e)
bexprToValueCondition (BinaryBExpr _ op e1 e2) = liftM2 (theOp op) (bexprToValueCondition e1) (bexprToValueCondition e2)
                where
                    theOp And = FOFAnd
                    theOp Or = FOFOr
bexprToValueCondition (RBinaryBExpr _ rel e1 e2) = liftM2 (theRel rel) (aexprToVExpr e1) (aexprToVExpr e2)
                where
                    theRel Equal x y = FOFAtom $ VAEq x y
                    theRel NotEqual x y = FOFNot $ FOFAtom $ VAEq x y
                    theRel Greater x y = FOFAtom $ VALt y x
                    theRel GreaterOrEqual x y = FOFNot $ FOFAtom $ VALt x y
                    theRel Less x y = FOFAtom $ VALt x y
                    theRel LessOrEqual x y = FOFNot $ FOFAtom $ VALt y x


--------------------------------------------
-- Symbolic execution of basic statements --
--------------------------------------------
symExLocalAssign :: 
                      (SymbStateLenses s, MonadRaise m, MonadLogger m, MonadState s m) =>
                      String -> AExpr -> m ()
symExLocalAssign target expr = do
                newval <- aexprToVExpr expr
                progVars %= Map.insert target newval

symExAllocate :: 
                   (MonadRaise m, MonadLogger m, Provers p, MonadReader p m,
                   SymbStateLenses s, MonadState s m, MonadIO m, MonadPlus m) =>
                   Maybe String -> AExpr -> m ()
symExAllocate target lenExpr = do
                lenval <- aexprToExpr lenExpr
                check $
                        -- Check that the length is positive
                        assertTrue $ VEConst 0 $<$ lenval
                loc <- newAvar $ fromMaybe "alloc" target
                producePredicate (PCells, [var loc, lenval])
                forM_ target $ \tvar -> progVars %= Map.insert tvar (var loc)

symExWrite :: (SymbStateLenses s, MonadLogger m, MonadRaise m, Provers p,
                     MonadReader p m, MonadIO m, MonadState s m, MonadPlus m) =>
                    AExpr -> AExpr -> m ()
symExWrite target expr = do
                loc <- aexprToExpr target
                check $ do
                        oldval <- newEvar "val"
                        consumePredicate (PCell, [loc, var oldval])
                newval <- aexprToExpr expr
                addPredicate (PCell, [loc, newval])

symExRead :: (SymbStateLenses s, MonadRaise m, MonadLogger m, Provers p,
                MonadReader p m, MonadIO m, MonadState s m, MonadPlus m) =>
               String -> AExpr -> m ()
symExRead target eloc = do
                loc <- aexprToExpr eloc
                oldval <- check $ do
                        oldval <- newEvar target
                        consumePredicate (PCell, [loc, var oldval])
                        return oldval
                addPredicate (PCell, [loc, var oldval])
                progVars %= Map.insert target (var oldval)

symExCAS :: (SymbStateLenses s, MonadRaise m, MonadLogger m, Provers p,
                MonadReader p m, MonadIO m, MonadState s m, MonadPlus m,
                MonadCut m) =>
                Maybe String -> AExpr -> AExpr -> AExpr -> m ()
symExCAS rtn target old new = do
                loc <- aexprToVExpr target
                oldv <- aexprToVExpr old
                newv <- aexprToVExpr new
                curv <- check $ do
                        curv <- newEvar "cas_val"
                        consumePredicate (PCell, [toExpr loc, var curv])
                        return curv
                branch_
                    (do -- success branch
                        assumeTrue $ VAEq (var curv) oldv
                        addPredicate (PCell, [toExpr loc, toExpr newv])
                        case rtn of
                            Nothing -> return ()
                            Just rtn' -> progVars %= Map.insert rtn' (VEConst 1)
                    )
                    (do -- failure branch
                        assumeFalse $ VAEq (var curv) oldv
                        addPredicate (PCell, [toExpr loc, var curv])
                        case rtn of 
                            Nothing -> return ()
                            Just rtn' -> progVars %= Map.insert rtn' (VEConst 0)
                    )


--}
