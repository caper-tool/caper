{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor, FlexibleContexts, MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, UndecidableInstances #-} 
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
import Data.List (intercalate)
import Data.Traversable
import Data.Maybe

import Caper.Utils.Failure
import Caper.Utils.NondetClasses

import Caper.Logger
import Caper.ProverStates
import qualified Caper.Utils.AliasingMap as AliasMap
import Caper.Parser.AST.Code
import Caper.Regions
import Caper.RegionTypes
import Caper.Exceptions
import Caper.Predicates
import Caper.Guards

-- default (ValueExpression VariableID, Integer, Double)


-- Symbolic States!
data SymbState = SymbState {
        _proverState :: Assumptions,
        _ssProgVars :: PVarBindings,
        _ssLogicalVars :: LVarBindings,
        _ssPreds :: Predicates,
        _ssRegions :: AliasMap.AliasMap VariableID Region,
        _ssOpenRegions :: [OpenRegion]
        }
makeLenses ''SymbState

emptySymbState :: SymbState
emptySymbState = SymbState emptyAssumptions Map.empty emptyLVars Map.empty AliasMap.empty []

showPVarBindings :: PVarBindings -> String
showPVarBindings = Map.foldWithKey showBinding ""
        where
                showBinding pv vr s = pv ++ " := " ++ show vr ++ "\n" ++ s

instance Show SymbState where
        show (SymbState p vs lvs prds regs oregs) = "Pure facts:\n" ++ show p 
                ++ "\nProgram variables:\n" ++ showPVarBindings vs 
                ++ "Heap:\n" ++ 
                (intercalate "\n" . 
                        map showPredicate . toPredicateList) prds


instance AssumptionLenses SymbState where
        bindings = proverState . bindings
        assumptions = proverState . assumptions
        assumptionVars = proverState . assumptionVars

class AssumptionLenses s => SymbStateLenses s where
        progVars :: Simple Lens s PVarBindings
        logicalVars :: Simple Lens s LVarBindings
        preds :: Simple Lens s Predicates

instance SymbStateLenses SymbState where
        progVars = ssProgVars
        logicalVars = ssLogicalVars
        preds = ssPreds

instance RegionLenses SymbState where
        regions = ssRegions
        openRegions = ssOpenRegions

instance SymbStateLenses s => SymbStateLenses (WithAssertions s) where
        progVars = withAssrBase . progVars
        logicalVars = withAssrBase . logicalVars
        preds = withAssrBase . preds

emptySymbStateWithVars :: [String] -> SymbState
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

showSymbState :: (MonadState SymbState m, MonadReader r m, RTCGetter r) => m String
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

printSymbState :: (MonadState SymbState m, MonadReader r m, RTCGetter r, MonadIO m) => m ()
printSymbState = showSymbState >>= liftIO . putStrLn

instance RTCGetter r => DebugState SymbState r where
    showState r s = show s ++ "\nRegions:\n" ++ show iregs
        where
            iregs = fmap inform (s ^. regions)
            inform reg = InformedRegion (reg, regTypeInstance reg >>=
                                \(RegionInstance rtid _) -> return $ (r ^. resolveRType) rtid)

instance RTCGetter r => DebugState (WithAssertions SymbState) r where
    showState r s@(WithAssertions {_withAssrBase = SymbState p vs lvs prds regs oregs}) =
        "Program variables:\n" ++ showPVarBindings vs 
        ++ "Heap:\n" ++ (intercalate "\n" . map showPredicate . toPredicateList) prds ++ "\n"
        ++ "\nRegions:\n" ++ show iregs
        ++ showAssertions s
        where
            iregs = fmap inform (s ^. regions)
            inform reg = InformedRegion (reg, regTypeInstance reg >>=
                                \(RegionInstance rtid _) -> return $ (r ^. resolveRType) rtid)

validatePredicate :: (MonadState s m, SymbStateLenses s, MonadReader r m, PredicateLenses r, MonadRaise m) => Predicate -> m ()
-- ^Check that a predicate has the correct number and type of parameters.
validatePredicate (n, exprs) = do
            predType <- resolvePredicateType n
            unless (length predType == length exprs) $
                raise $ ArgumentCountMismatch (length exprs) (length predType)
            chkTypes exprs predType
        where
                chkTypes (e : es) (t : ts) = checkExpressionAtType e t >> chkTypes es ts
                chkTypes _ _ = return ()


predicateAssumptions :: Predicate -> Predicates -> [Condition VariableID]
predicateAssumptions (PCell, e1 : _) prds = toCondition (VALt (VEConst 0) e0) :
                foldMap genCond (Map.findWithDefault MultiSet.empty PCell prds) ++
                foldMap genCellsCond (Map.findWithDefault MultiSet.empty PCells prds)
        where
                genCond (e1' : _) = [negativeCondition $ VAEq (toValueExpr e1') e0]
                genCond _ = error "predicateAssumptions: Bad #cell predicate"
                e0 = toValueExpr e1
                genCellsCond [a,l] = [toCondition (FOFOr (FOFAtom (VALt e0 (toValueExpr a))) (FOFNot $ FOFAtom (VALt e0 (VEPlus (toValueExpr a) (toValueExpr l)))))]
                genCellsCond _ = error "predicateAssumptions: Bad #cells predicate"
predicateAssumptions (PCells, [e1, e2]) prds = [toCondition (VALt (VEConst 0) e1'),  toCondition (VALt (VEConst 0) e2')] ++
                foldMap genCellCond (Map.findWithDefault MultiSet.empty PCell prds) ++
                foldMap genCellsCond (Map.findWithDefault MultiSet.empty PCells prds)
        where
                e1' = toValueExpr e1
                e2' = toValueExpr e2
                genCellCond (a : _) = [toCondition (FOFOr (FOFAtom (VALt (toValueExpr a) e1')) (FOFNot $ FOFAtom (VALt (toValueExpr a) (VEPlus e1' e2'))))]
                genCellCond _ = error "predicateAssumptions: Bad #cell predicate"
                genCellsCond [a,l] = let
                        a' = toValueExpr a
                        l' = toValueExpr l in
                        [toCondition (FOFOr 
                                (FOFNot $ FOFAtom $ VALt a' (VEPlus e1' e2'))
                                (FOFNot $ FOFAtom $ VALt e1' (VEPlus a' l')))]
                genCellsCond _ = error "predicateAssumptions: Bad #cells predicate"

predicateAssumptions _ _ = []

generatePredicateAssumptions :: (MonadState s m, SymbStateLenses s) => Predicate -> m ()
generatePredicateAssumptions p = do
                                ps <- use preds
                                mapM_ assume (predicateAssumptions p ps)

insertPredicate :: Predicate -> Predicates -> Predicates
insertPredicate (n, es) = Map.insertWith (flip MultiSet.union) n (MultiSet.singleton es)

mergePredicates :: Predicates -> Predicates -> Predicates
mergePredicates = Map.unionWith MultiSet.union

addPredicate :: (MonadState s m, SymbStateLenses s) => Predicate -> m ()
addPredicate p = preds %= insertPredicate p
                
producePredicate :: (MonadState s m, SymbStateLenses s, MonadReader r m, PredicateLenses r, MonadRaise m) => Predicate -> m ()
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

consumeCellAny :: (MonadPlus m, MonadState s m, MonadLogger m, MonadLabel CapturedState m, MonadReader r m, DebugState s r,
        AssertionLenses s, SymbStateLenses s) => Expr VariableID -> Expr VariableID -> m ()
consumeCellAny x y = (do
                [e1,e2] <- takingEachPredInstance PCell
                labelS $ "Consume " ++ show x ++ "|->" ++ show y ++ " from " ++ show e1 ++ "|->" ++ show e2
                assertEqual x e1
                assertEqual y e2) `mplus`
        (do
                [e1,e2] <- takingEachPredInstance PCells
                labelS $ "Consume " ++ show x ++ "|->" ++ show y ++ " from " ++ show e1 ++ "|->#cells(" ++ show e2 ++ ")"
                assertTrue $ e1 $<=$ x
                assertTrue $ x $<$ e1 $+$ e2
                yval <- newAvar "unk"
                assertEqual y (var yval)
                (labelS "At left" >> assertEqual e1 x) `mplus`
                    (do
                        labelS "Not at left"
                        addPredicate (PCells, [e1, toExpr (x $-$ e1)])
                        assertTrue $ e1 $<$ x)
                (labelS "At right" >> assertEqual (e1 $+$ e2) (x $+$ VEConst 1)) `mplus`
                    (do
                        labelS "Not at right"
                        addPredicate (PCells, [toExpr (x $+$ VEConst 1), toExpr (e1 $+$ e2 $-$ x $-$ VEConst 1)])
                        assertTrue $ (x $+$ VEConst 1) $<$ (e1 $+$ e2)))
                -- add justCheck to fail faster?

-- |Consumes a predicate.  Does not check that the predicate is well-formed.
-- 
-- FIXME: Case handling for PCells and other predicates
consumePred :: (Monad m, MonadPlus m, MonadState s m, MonadLogger m, MonadLabel CapturedState m, MonadReader r m, DebugState s r,
        AssertionLenses s, SymbStateLenses s) => Predicate -> m ()
consumePred (PCell, [x, y]) = do
                prds <- use preds
                let ps = MultiSet.distinctElems (MultiSet.filter ((x ==) . head) (predicateLookup PCell prds))
                if null ps then consumeCellAny x y else do
                        p@[e1,e2] <- chooseFrom ps
                        preds %= Map.adjust (MultiSet.delete p) PCell
                        unless (x == e1) $ error "consumePred went wrong"
                        assertEqual y e2
consumePred p@(pt, args) = do
                args' <- takingEachPredInstance pt
                forM_ (zip args args') $ uncurry assertEqual


-- |Consumes a predicate, after checking that it is well-formed.
--
-- TODO: This should not be used as-is; it should be changed so that validation
-- failures raise exceptions and some kind of context is used for resolving the
-- number/type information for validation.
--
-- TD-Y: I'm going to use this stuff as is; at some point the front-end will be
-- redesigned to simplify the parser and provide an input validation/type-
-- checking phase.
consumePredicate :: 
                      (SymbStateLenses s, AssertionLenses s, MonadLogger m, MonadLabel CapturedState m,
                       MonadState s m, MonadPlus m, MonadReader r m, PredicateLenses r, MonadRaise m, DebugState s r) =>
                      Predicate -> m ()
consumePredicate p = do
                validatePredicate p
                consumePred p

-- |Remove all resources (predicate and region), returning an operation
-- that will restore them. 
frame :: (MonadState s m, SymbStateLenses s, RegionLenses s,
        MonadReader r m, RTCGetter r, Provers r, DebugState s r,
        MonadLogger m, MonadRaise m, MonadIO m, MonadDemonic m, MonadLabel CapturedState m) =>
        m (m ())
frame = do
        stabiliseRegions
        prds <- use preds
        preds .= Map.empty
        regs <- use regions
        regions .= fmap (\r -> r {regState = Nothing, regGuards = emptyGuard}) regs
        return $ do
            preds %= mergePredicates prds
            forM_ (AliasMap.toRootList regs) $ \(rid, rg) -> do
                (Just rg') <- liftM (AliasMap.lookup rid) $ use regions
                rg'' <- mergeRegions rg rg'
                regions . ix rid .= rg'' 

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
                   (MonadRaise m, MonadLogger m, Provers p, PredicateLenses p, MonadReader p m, DebugState (WithAssertions s) p,
                   SymbStateLenses s, MonadState s m, MonadIO m, MonadPlus m, MonadLabel CapturedState m, OnFailure f m, AbductionFailure f, MonadOrElse m) =>
                   Maybe String -> AExpr -> m ()
symExAllocate target lenExpr = do
                lenval <- aexprToExpr lenExpr
                check $
                        -- Check that the length is positive
                        assertTrue $ VEConst 0 $<$ lenval
                loc <- newAvar $ fromMaybe "alloc" target
                producePredicate (PCells, [var loc, lenval])
                forM_ target $ \tvar -> progVars %= Map.insert tvar (var loc)

symExWrite :: (SymbStateLenses s, MonadLogger m, MonadRaise m, Provers p, PredicateLenses p, DebugState (WithAssertions s) p,
                     MonadReader p m, MonadIO m, MonadState s m, MonadPlus m, MonadLabel CapturedState m, OnFailure f m, AbductionFailure f, MonadOrElse m) =>
                    AExpr -> AExpr -> m ()
symExWrite target expr = do
                loc <- aexprToExpr target
                check $ do
                        oldval <- newEvar "val"
                        consumePredicate (PCell, [loc, var oldval])
                newval <- aexprToExpr expr
                addPredicate (PCell, [loc, newval])

symExRead :: (SymbStateLenses s, MonadRaise m, MonadLogger m, Provers p, PredicateLenses p, DebugState (WithAssertions s) p,
                MonadReader p m, MonadIO m, MonadState s m, MonadPlus m, MonadLabel CapturedState m, OnFailure f m, AbductionFailure f, MonadOrElse m) =>
               String -> AExpr -> m ()
symExRead target eloc = do
                loc <- aexprToExpr eloc
                oldval <- check $ do
                        oldval <- newEvar target
                        consumePredicate (PCell, [loc, var oldval])
                        return oldval
                addPredicate (PCell, [loc, var oldval])
                progVars %= Map.insert target (var oldval)

symExCAS :: (SymbStateLenses s, MonadRaise m, MonadLogger m, Provers p, PredicateLenses p,
                MonadReader p m, MonadIO m, MonadState s m, MonadPlus m, DebugState s p, DebugState (WithAssertions s) p,
                MonadDemonic m, MonadLabel CapturedState m, OnFailure f m, AbductionFailure f, MonadOrElse m) =>
                Maybe String -> AExpr -> AExpr -> AExpr -> m ()
symExCAS rtn target old new = do
                loc <- aexprToVExpr target
                oldv <- aexprToVExpr old
                newv <- aexprToVExpr new
                curv <- check $ do
                        curv <- newEvar "cas_val"
                        consumePredicate (PCell, [toExpr loc, var curv])
                        return curv
                (do -- success branch
                        labelS "CAS succeeds"
                        assumeTrue $ VAEq (var curv) oldv
                        addPredicate (PCell, [toExpr loc, toExpr newv])
                        case rtn of
                            Nothing -> return ()
                            Just rtn' -> progVars %= Map.insert rtn' (VEConst 1)
                    ) <#>
                    (do -- failure branch
                        labelS "CAS fails"
                        assumeFalse $ VAEq (var curv) oldv
                        addPredicate (PCell, [toExpr loc, var curv])
                        case rtn of 
                            Nothing -> return ()
                            Just rtn' -> progVars %= Map.insert rtn' (VEConst 0)
                    )


--}
