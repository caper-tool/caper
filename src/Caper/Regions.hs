{-# LANGUAGE MultiParamTypeClasses #-}
{- Regions -}
module Caper.Regions where
import Prelude hiding (mapM_,mapM,concat,any,foldl,concatMap)
import Control.Monad.State hiding (mapM_,mapM,forM_,msum)
import Control.Monad.Reader hiding (mapM_,mapM,forM_,msum)
import Control.Monad.Trans.Maybe
import Control.Lens hiding (op)
import Data.Foldable
import Data.Traversable
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.List (partition)

import Caper.Utils.NondetClasses
import Caper.Utils.AliasingMap (AliasMap)
import qualified Caper.Utils.AliasingMap as AM

import Caper.Parser.AST.Annotation (TopLevelGuardDeclr(..))

import Caper.RegionTypes
import Caper.Logger
import Caper.Exceptions
import Caper.ProverDatatypes
import Caper.Prover -- TODO: move some stuff from Prover to ProverDatatypes?
import Caper.ProverStates
import Caper.Guards
import Caper.Transitions

import Debug.Trace

data RegionInstance = RegionInstance {
        riType :: RTId,
        riParameters :: [Expr VariableID]
}

data Region = Region {
        regDirty :: Bool,
        regTypeInstance :: Maybe RegionInstance,
        regState :: Maybe (ValueExpression VariableID),
        regGuards :: Guard VariableID
}

class RegionLenses a where
        regions :: Simple Lens a (AliasMap VariableID Region)
        openRegions :: Simple Lens a [VariableID]
        

instance RegionLenses s => RegionLenses (WithAssertions s) where
        regions = withAssrBase . regions
        openRegions = withAssrBase . openRegions

regionList :: (MonadState s m, RegionLenses s) => m [VariableID]
regionList = liftM AM.distinctKeys $ use regions

-- TODO: possibly move somewhere more relevant
mergeMaybe :: (Monad m) => (a -> a -> m a) -> Maybe a -> Maybe a -> m (Maybe a)
mergeMaybe _ Nothing m2 = return m2
mergeMaybe _ m1 Nothing = return m1
mergeMaybe op (Just m1) (Just m2) = liftM Just (op m1 m2)


-- |Merge region instances, adding equality assumptions between parameters
--
-- Pre: region instances should be checked against their types; i.e.
-- if they have the same region type, then they must have the same number
-- and type of parameters.
mergeRegionInstances :: (MonadState s m, AssumptionLenses s) => RegionInstance -> RegionInstance -> m RegionInstance
mergeRegionInstances i1@(RegionInstance t1 ps1) i2@(RegionInstance t2 ps2)
        = (if t1 /= t2 then
                -- These regions cannot be the same, so assume false!
                assumeContradiction
          else forM_ (zip ps1 ps2) $ \(p1, p2) ->
                        -- The precondition should guarantee against an error
                        -- in exprEquality.
                        assume $ exprEquality p1 p2)
          >> return i1

mergeValueExpressions :: (MonadState s m, AssumptionLenses s) =>
        ValueExpression VariableID ->
        ValueExpression VariableID -> m (ValueExpression VariableID)
mergeValueExpressions ve1 ve2 = assumeTrue (ve1 $=$ ve2) >> return ve1

mergeRegions :: (MonadState s m, AssumptionLenses s, MonadReader r m, RTCGetter r) =>
        Region -> Region -> m Region
mergeRegions r1 r2 = do
                let dirty = regDirty r1 || regDirty r2
                ti <- mergeMaybe mergeRegionInstances (regTypeInstance r1) (regTypeInstance r2)
                s <- mergeMaybe mergeValueExpressions (regState r1) (regState r2)
                g <- mergeGuards (regGuards r1) (regGuards r2)
                case ti of
                        (Just (RegionInstance rtid _)) -> do
                                res <- view resolveRType
                                let gt = rtWeakGT $ res rtid
                                unless (checkGuardAtType g gt) assumeContradiction
                        _ -> return ()
                return $ Region dirty ti s g


-- FIXME: Add bound information!
-- | Add a region, or merge it if one already exists with the same identifier.
--
-- Pre: the number and type of arguments should have been checked (otherwise an error may arise).
produceMergeRegion :: (MonadState s m, AssumptionLenses s, RegionLenses s,
                MonadReader r m, RTCGetter r) =>
                VariableID -> Region -> m ()
produceMergeRegion rvar region = do
                regs <- use regions
                case AM.lookup rvar regs of
                        Nothing -> regions .= AM.insert rvar region regs
                        (Just r) -> do
                                r' <- mergeRegions r region
                                regions .= AM.overwrite rvar r' regs


-- XXX: This is overkill.  In all but very few cases the rid should already
-- point to a region.
consumeRegion :: (MonadState s m, AssertionLenses s, RegionLenses s,
                MonadReader r m, RTCGetter r,
                MonadPlus m,
                MonadLogger m) =>
                RTId                    -- ^Type of the region 
                -> VariableID           -- ^Identifier variable 
                -> [Expr VariableID]    -- ^Parameters
                ->  ValueExpression VariableID     -- ^State
                -> m ()
consumeRegion rtid rid params st = do
        -- Check if rid already identifies a region
        regs <- use regions
        case regs ^? ix rid of
                Just reg -> do -- It does!
                        (RegionInstance artid aparams) <- liftMaybe
                                (regTypeInstance reg)
                        if artid == rtid then do
                                bindParams aparams
                                bindState $ regState reg
                            else
                                mzero -- Type doesn't match!
                Nothing -> do
                        -- No region, so we'll simply try all those of the
                        -- right type
                        let crs = filter okRegionType (AM.toRootList regs)
                        (arid, Region _ (Just (RegionInstance _ aparams))
                                                         astate _)
                                <- chooseFrom crs
                        -- Bind the identifier
                        assert (EqualityCondition rid arid)
                        bindParams aparams
                        bindState astate
    where
        okRegionType (_, Region _ (Just (RegionInstance rtid0 _)) _ _) =
                rtid0 == rtid
        okRegionType _ = False
        bindParams aparams = mapM_ assert $ zipWith exprEquality params aparams
        bindState (Just ast) = assertTrue $ VAEq st ast
        bindState Nothing = newAvar "state" >>=
                        assertTrue . VAEq st . var
                

-- |Determine if two variables cannot be aliases for the same region.
-- It may be possible that variables can be proved not to be aliases,
-- but this routine may still treat them as if they could be.
cannotAlias :: (MonadState s m, RegionLenses s) => VariableID -> VariableID -> m Bool
cannotAlias r1 r2
        | r1 == r2 = return False
        | otherwise = do
                regs <- use regions
                return $ case (regs ^? ix r1 >>= regTypeInstance, regs ^? ix r2 >>= regTypeInstance) of
                    (Just rt1, Just rt2) -> riType rt1 /= riType rt2
                    _ -> False


{-
-- For now, I'm not going to use this, in favour of cannotAliasStrong.
cannotAliasRegs :: AliasMap VariableID Region -> VariableID -> VariableID -> Bool
cannotAliasRegs regs r1 r2
        | r1 == r2 = False
        | otherwise = case (regs ^? ix r1 >>= regTypeInstance, regs ^? ix r2 >>= regTypeInstance) of
                    (Just rt1, Just rt2) -> riType rt1 /= riType rt2
                    _ -> False
-}
-- TODO: Put somewhere more appropriate?
restoring :: (MonadState s m) => m a -> m a
-- ^Run a stateful computation, restoring the state at the beginning.
restoring f = do
            s <- get
            r <- f
            put s
            return r 
                   
-- |Determine if two variables cannot be aliases for the same region.
-- It may be possible that variables can be proved not to be aliases,
-- but this routine may still treat them as if they could be.
-- This version gives fewer false negatives than cannotAlias, but requires
-- calls to provers to see if a merge can take place.
cannotAliasStrong :: (ProverM s r m, RegionLenses s, RTCGetter r) => VariableID -> VariableID -> m Bool
cannotAliasStrong r1 r2
        | r1 == r2 = return False
        | otherwise = do
                    -- Try merging the regions.  If the result is
                    -- inconsistent then the regions are not aliases.
                    regs <- use regions
                    case (regs ^? ix r1, regs ^? ix r2) of
                        (Just reg1, Just reg2) -> restoring $ do
                                _ <- mergeRegions reg1 reg2
                                c <- isConsistent
                                return (c == Just False)
                        _ -> return False
                        

-- |Stabilise all regions
stabiliseRegions :: (ProverM s r m, RegionLenses s, RTCGetter r, MonadRaise m) =>
                        m ()
stabiliseRegions = do
                        regs <- use regions
                        regs' <- mapM stabiliseRegion regs
                        regions .= regs'

{-
-- Stabilise a region (only if it is dirty)
stabiliseRegion :: (ProverM s r m, RTCGetter r) =>
                        Region -> m Region
stabiliseRegion reg = if regDirty reg then
                                stabiliseDirtyRegion reg
                        else
                                return reg -}

-- Stabilise a region
stabiliseRegion :: (ProverM s r m, RTCGetter r, MonadRaise m) =>
                        Region -> m Region
-- Not dirty, so nothing to do!
stabiliseRegion
        reg@(Region False _ _ _) = return reg
-- Here we know enough about the region that we have to do something
stabiliseRegion
        (Region _ rti@(Just (RegionInstance rtid ps)) (Just se) gd) = do
                        -- resolve region type
                        rt <- lookupRType rtid
                        transitions <- (trace $ "Checking transitions: " ++ show rt ++ " " ++ show ps ++ " " ++ show gd) checkTransitions rt ps gd
                        -- compute the closure relation
                        tcrel <- computeClosureRelation (rtStateSpace rt) transitions
                        -- create a new state variable
                        newStateVar <- newAvar "state"
                        -- assume it is related to the old state
                        assumeTrue $ tcrel se (var newStateVar)
                        -- return the clean region with the new state
                        return $ Region
                                False
                                rti
                                (Just (var newStateVar))
                                gd
-- In this case, we don't know the region type, or don't know the
-- region state, in which case we don't know the stabilised region
-- state.
stabiliseRegion r = return $ r {regDirty = False, regState = Nothing}

-- |Determine a list of possible environment (rely) transitions for a given
-- parametrised region type and guard.
--
-- TODO: Account for action conditions
checkTransitions :: (ProverM s r m, MonadRaise m) => RegionType -> [Expr VariableID] -> Guard VariableID -> m [GuardedTransition VariableID]
checkTransitions rt ps gd = liftM concat $ mapM checkTrans (rtTransitionSystem rt)
        where
                bndVars tr = Set.difference (trVariables tr) (rtParamVars rt)
                params = Map.fromList $ zip (map fst $ rtParameters rt) ps
                checkTrans tr@(TransitionRule trgd prd prec post) = do
                        -- Compute a binding for fresh variables
                        bvmap <- freshInternals rtdvStr (bndVars tr)
                        let bvars = Map.elems bvmap
                        let subst = Map.union params $ fmap var bvmap
                        let s v = Map.findWithDefault (error "checkTransitions: variable not found") v subst
                        let isDynVar = (`Set.member` Set.fromList (concatMap toList [prec, post]))
                        -- The list of conditions for the transition rule can be divided into:
                        -- * Static conditions, which are independent of the state transition; and
                        -- * Dynamic conditions, which may constrain the state transition (and can only depend on values)
                        let (dyconds, stconds) = partition (any isDynVar) prd 
                        -- Checking guard compatibility may generate some conditions (as assertions) that may constrain the transition
                        -- However, since parametrised guards are not yet implemented, that actually can't happen (yet!)
                        -- Now have to check if guard is applicable!
                        guardCompat <- hypothetical $ do
                                -- assume the static conditions
                                mapM_ (assume . exprCASub' s) stconds
                                -- combine guards
                                gd' <- mergeGuards gd (exprSub s trgd)
                                assms <- use assumptions
                                -- check the guard matches the guard type
                                if checkGuardAtType gd' (topLevelToWeakGuardType $ rtGuardType rt) then
                                        -- and is consistent
                                        isConsistent
                                    else
                                        return $ Just False
                        if guardCompat == Just False then return [] else do
                                cond <- foldlM (\x -> liftM (FOFAnd x . exprCASub' s) . toValueFOF isDynVar) FOFTrue dyconds
                                return [GuardedTransition bvars cond (exprSub s prec) (exprSub s post)]

-- |Determine a list of possible thread (guarantee) transitions for a given
-- parametrised region type and guard.
checkGuaranteeTransitions :: (ProverM s r m, MonadRaise m) => RegionType -> [Expr VariableID] -> Guard VariableID -> m [GuardedTransition VariableID]
checkGuaranteeTransitions rt ps gd = liftM concat $ mapM checkTrans (rtTransitionSystem rt)
        where
                bndVars tr = Set.difference (trVariables tr) (rtParamVars rt)
                params = Map.fromList $ zip (map fst $ rtParameters rt) ps
                checkTrans tr@(TransitionRule trgd prd prec post) = do
                        -- Compute a binding for fresh variables
                        bvmap <- freshInternals rtdvStr (bndVars tr)
                        let bvars = Map.elems bvmap
                        let subst = Map.union params $ fmap var bvmap
                        let s v = Map.findWithDefault (error "checkGuaranteeTransitions: variable not found") v subst
                        let isDynVar = (`Set.member` Set.fromList (concatMap toList [prec, post]))
                        -- The list of conditions for the transition rule can be divided into:
                        -- * Static conditions, which are independent of the state transition; and
                        -- * Dynamic conditions, which may constrain the state transition (and can only depend on values)
                        let (dyconds, stconds) = partition (any isDynVar) prd 
                        -- Consuming the guard may generate some conditions (as assertions) that may constrain the transition
                        -- However, since parametrised guards are not yet implemented, that actually can't happen (yet!)
                        -- Now have to check if guard is available.
                        transitionImpossible <- liftM isNothing $
                             get >>= \ss -> runMaybeT $ flip evalStateT (emptyWithAssertions ss) $ do
                                mapM_ (assert . exprCASub' s) stconds
                                case rtGuardType rt of
                                    ZeroGuardDeclr -> return ()
                                    SomeGuardDeclr gdec -> do
                                            _ <- guardEntailment gdec gd (exprSub s trgd)
                                            return ()
                                justCheck
                        case transitionImpossible of
                            True -> return []
                            False -> do
                                cond <- foldlM (\x -> liftM (FOFAnd x . exprCASub' s) . toValueFOF isDynVar) FOFTrue dyconds
                                return [GuardedTransition bvars cond (exprSub s prec) (exprSub s post)]


toValueFOF :: (MonadRaise m, Monad m) => (v -> Bool) -> Condition v -> m (FOF ValueAtomic v)
toValueFOF varTest (ValueCondition v) = return v
toValueFOF varTest (PermissionCondition pc) = case find varTest pc of
                                Nothing -> error "Caper.Regions.toValueFOF: internal error"
                                Just v -> raise $ TypeMismatch VTPermission VTValue
toValueFOF varTest (EqualityCondition v1 v2) = return $ FOFAtom $ VAEq (var v1) (var v2)
toValueFOF varTest (DisequalityCondition v1 v2) = return $ FOFNot $ FOFAtom $ VAEq (var v1) (var v2)

-- |Generate a 'Condition' that captures the fact that two abstract
-- states must be related by the guarantee for a region.   
generateGuaranteeCondition :: (ProverM s r m, MonadRaise m) =>
    RegionType                      -- ^Type of the region
    -> [Expr VariableID]            -- ^Parameters for the region
    -> Guard VariableID             -- ^Guard for the region
    -> ValueExpression VariableID   -- ^Old state
    -> ValueExpression VariableID   -- ^New state
        -> m (Condition VariableID)
generateGuaranteeCondition rt params gd st0 st1 = do
        transitions <- checkGuaranteeTransitions rt params gd
        rel <- underComputeClosureRelation (rtStateSpace rt) transitions
        return $ ValueCondition (rel st0 st1)


-- |Get the region type and parameters for a region.  If no type is available
-- (because the variable does not identify a region or the region's type is
-- not known) it will return Nothing.  It can throw an error if a region
-- has an invalid region type identifier.
getTypeOfRegion :: (MonadState s m, RegionLenses s, MonadReader r m, RTCGetter r) =>
            VariableID -> m (Maybe (RegionType, [Expr VariableID]))
getTypeOfRegion rid = do
            regs <- use regions
            case regs ^? ix rid >>= regTypeInstance of
                Nothing -> return Nothing
                Just (RegionInstance rtid ps) -> do
                        rt <- lookupRType rtid
                        return $ Just (rt, ps) 
-- Check if a guard is compatible 
