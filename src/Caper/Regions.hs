{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts #-}
{- Regions -}
module Caper.Regions where
import Prelude hiding (mapM_,mapM,concat,any,foldl,concatMap,foldr)
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
import Caper.Utils.Choice
import Caper.Utils.AliasingMap (AliasMap)
import qualified Caper.Utils.AliasingMap as AM

import Caper.Parser.AST.Annotation (TopLevelGuardDeclr(..))

import Caper.RegionTypes
import Caper.Logger
import Caper.Exceptions
import Caper.ProverDatatypes
import Caper.Prover -- TODO: move some stuff from Prover to ProverDatatypes?
import Caper.DeductionFailure
import Caper.ProverStates
import Caper.Guards
import Caper.Transitions
import Caper.FirstOrder

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
                MonadPlus m, Failure DeductionFailure m,
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
                                <- chooseFrom crs `mplus` 
                                    (get >>= \s -> failure (MissingRegionByType rtid params st s))
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
                                assume (EqualityCondition r1 r2)
                                c <- isConsistent
                                return (c == Just False)
                        _ -> return False
                        

-- |Stabilise all regions
stabiliseRegions :: (ProverM s r m, RegionLenses s, RTCGetter r, DebugState s r, MonadRaise m) =>
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
stabiliseRegion :: (ProverM s r m, RTCGetter r, DebugState s r, MonadRaise m) =>
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
                        tcrel <- rely rt transitions -- computeClosureRelation (rtStateSpace rt) transitions
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
                where
                        rely rt transitions
                                | rtIsTransitive rt = return $ \x y -> foldr (FOFOr . gtToFOF x y) (FOFAtom $ VAEq x y) transitions
                                | otherwise = computeClosureRelation (rtStateSpace rt) transitions
                        gtToFOF :: ValueExpression VariableID -> ValueExpression VariableID -> GuardedTransition VariableID -> FOF ValueAtomic VariableID
                        gtToFOF x y (GuardedTransition bvs cond e1 e2) =
                                let sub = freshSub bvs (Set.fromList $ toList x ++ toList y ++ bvs ++ toList cond ++ toList e1 ++ toList e2) in
                                let sub' = VEVar . sub in
                                    foldr (FOFExists . sub) (FOFAnd (FOFAnd (FOFAtom $ VAEq x (exprSub sub' e1)) (FOFAtom $ VAEq y (exprSub sub' e2))) (exprCASub sub' cond)) bvs
                                -- Rename bvs so that they don't clash with variables in x and y (also cond e1 and e2)
-- In this case, we don't know the region type, or don't know the
-- region state, in which case we don't know the stabilised region
-- state.
stabiliseRegion r = return $ r {regDirty = False, regState = Nothing}

-- |Determine a list of possible environment (rely) transitions for a given
-- parametrised region type and guard.
checkTransitions :: (ProverM s r m, DebugState s r, MonadRaise m) => RegionType -> [Expr VariableID] -> Guard VariableID -> m [GuardedTransition VariableID]
checkTransitions rt ps gd = liftM concat $ mapM checkTrans (rtTransitionSystem rt)
        where
                bndVars :: TransitionRule -> Set.Set RTDVar
                bndVars tr = Set.difference (freeVariables tr) (rtParamVars rt)
                params = Map.fromList $ zip (map fst $ rtParameters rt) ps
                checkTrans tr@(TransitionRule trgd prd prec post) = do
                        -- Compute a binding for fresh variables
                        bvmap <- freshInternals rtdvStr (bndVars tr)
                        liftIO $ print tr
                        liftIO $ print $ freeVariables tr
                        let bvars = Map.elems bvmap
                        let subst = Map.union params $ fmap var bvmap
                        let s v = Map.findWithDefault (error "checkTransitions: variable not found") v subst
                        -- Now have to check if guard is applicable!
                        guardCompat <- hypothetical $ do
                                -- assume conditions
                                mapM_ (assume . exprCASub' s) prd
                                -- combine guards
                                gd' <- mergeGuards gd (exprCASub' s trgd)
                                -- We extract the assumptions that condition the transition.
                                -- That is, those that have variables which are locally bound for
                                -- the action, and occur in either the pre- or post-state.
                                -- These variables are bound to be value variables, and so all such
                                -- conditions will be value-convertible.
                                assms <- use assumptions
                                let isDynVar = (`Set.member` Set.fromList (concatMap toList [prec, post]))
                                let cvars = Map.elems $ Map.filterWithKey (\k _ -> isDynVar k) bvmap
                                let isCvar = (`Set.member` Set.fromList cvars)
                                let cassms = filter (any isCvar . freeVariables) assms
                                -- check the guard matches the guard type
                                if checkGuardAtType gd' (topLevelToWeakGuardType $ rtGuardType rt) then
                                        -- and is consistent
                                        isConsistent >>= \x -> case x of
                                          Just False -> return $ Left ()
                                          _ -> return $ Right cassms
                                    else
                                        return $ Left ()
                        case guardCompat of
                          Left _ -> return []
                          Right cassms -> do
                            liftIO $ putStrLn $ "Transition conditions for: " ++ show bvars ++ " " ++ (show (exprSub s prec)) ++ " ~> " ++ show (exprSub s post)
                            liftIO $ mapM_ print cassms
                            let cond = foldBy FOFAnd FOFTrue $ valueConditions (const True) cassms
                            return [GuardedTransition bvars cond (exprSub s prec) (exprSub s post)]

-- |Determine a list of possible thread (guarantee) transitions for a given
-- parametrised region type and guard.
checkGuaranteeTransitions :: (ProverM (WithAssertions s) r m, AssumptionLenses s, DebugState (WithAssertions s) r, MonadRaise m) => RegionType -> [Expr VariableID] -> Guard VariableID -> m [GuardedTransition VariableID]
checkGuaranteeTransitions rt ps gd = liftM concat $ mapM checkTrans (rtTransitionSystem rt)
        where
                bndVars :: TransitionRule -> Set.Set RTDVar
                bndVars tr = Set.difference (freeVariables tr) (rtParamVars rt)
                params = Map.fromList $ zip (map fst $ rtParameters rt) ps
                checkTrans tr@(TransitionRule trgd prd prec post) = do
                        -- Compute a binding for fresh variables
                        bvmap <- freshInternals rtdvStr (bndVars tr)
                        let bvars = Map.elems bvmap
                        let subst = Map.union params $ fmap var bvmap
                        let s v = Map.findWithDefault (error "checkGuaranteeTransitions: variable not found") v subst
                        -- The list of conditions for the transition rule can be divided into:
                        -- - Static conditions, which are independent of the state transition; and
                        -- - Dynamic conditions, which may constrain the state transition (and can only depend on values)
                        -- let (dyconds, stconds) = partition (any isDynVar) prd 
                        -- Consuming the guard may generate some conditions (as assertions) that may constrain the transition
                        -- However, since parametrised guards are not yet implemented, that actually can't happen (yet!)
                        -- Now have to check if guard is available.
                        conds <-
                             get >>= \ss -> allChoices $ flip evalStateT ss $ do
                                mapM_ declareEvar bvars
                                mapM_ (assert . exprCASub' s) prd
                                case rtGuardType rt of
                                    ZeroGuardDeclr -> return ()
                                    SomeGuardDeclr gdec -> do
                                            _ <- guardEntailment gdec gd (exprCASub' s trgd)
                                            return ()
                                liftIO $ putStrLn "Entailment for guarantee"
                                debugState
                                justCheck
                                liftIO $ putStrLn "passed"
                                -- We extract the assertions that condition the transition.
                                -- That is, those that have variables which are locally bound for
                                -- the action and occur in either the pre- or post-state.
                                -- These variables are bound to be value variables, and so all such
                                -- conditions will be value-convertible.
                                assrts <- use assertions
                                let isDynVar = (`Set.member` Set.fromList (concatMap toList [prec, post]))
                                let cvars = Map.elems $ Map.filterWithKey (\k _ -> isDynVar k) bvmap
                                let isCvar = (`Set.member` Set.fromList cvars)
                                let cassrts = filter (any isCvar . freeVariables) assrts
                                return cassrts
                        let condToTrans cassrts =
                                let cond = foldBy FOFAnd FOFTrue $ valueConditions (const True) cassrts in
                                GuardedTransition bvars cond (exprSub s prec) (exprSub s post)
                        return (map condToTrans conds)
                        {-case conds of
                            Nothing -> return []
                            Just cassrts -> do
                                --cond <- foldlM (\x -> liftM (FOFAnd x . exprCASub' s) . toValueFOF isDynVar) FOFTrue dyconds
                                let cond = foldBy FOFAnd FOFTrue $ valueConditions (const True) cassrts
                                return [GuardedTransition bvars cond (exprSub s prec) (exprSub s post)] -}

{-
toValueFOF :: (MonadRaise m, Monad m) => (v -> Bool) -> Condition v -> m (FOF ValueAtomic v)
toValueFOF varTest (ValueCondition v) = return v
toValueFOF varTest (PermissionCondition pc) = case find varTest pc of
                                Nothing -> error "Caper.Regions.toValueFOF: internal error"
                                Just v -> raise $ TypeMismatch VTPermission VTValue
toValueFOF varTest (EqualityCondition v1 v2) = return $ FOFAtom $ VAEq (var v1) (var v2)
toValueFOF varTest (DisequalityCondition v1 v2) = return $ FOFNot $ FOFAtom $ VAEq (var v1) (var v2)
-}

-- |Generate a 'Condition' that captures the fact that two abstract
-- states must be related by the guarantee for a region.   
generateGuaranteeCondition :: (ProverM (WithAssertions s) r m, AssumptionLenses s, DebugState (WithAssertions s) r, MonadRaise m) =>
    RegionType                      -- ^Type of the region
    -> [Expr VariableID]            -- ^Parameters for the region
    -> Guard VariableID             -- ^Guard for the region
    -> ValueExpression VariableID   -- ^Old state
    -> ValueExpression VariableID   -- ^New state
        -> m (Condition VariableID)
generateGuaranteeCondition rt params gd st0 st1
    | rtIsTransitive rt = do
        transitions <- checkGuaranteeTransitions rt params gd
        liftIO $ putStrLn $ "Guarantee transitions: " ++ show transitions
        return $ ValueCondition $ foldl FOFOr (st0 $=$ st1) $ do
            GuardedTransition bvars cond e0 e1 <- transitions
            let c = FOFAnd (FOFAnd (st0 $=$ e0) (st1 $=$ e1)) cond
            return $ foldr FOFExists c bvars
    | otherwise = do
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
