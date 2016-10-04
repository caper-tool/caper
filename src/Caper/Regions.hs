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

import Caper.Utils.NondetClasses
import Caper.Utils.Choice
import Caper.Utils.AliasingMap (AliasMap)
import qualified Caper.Utils.AliasingMap as AM

import Caper.Parser.AST.Annotation (TopLevelGuardDeclr(..))

import Caper.RegionTypes
import Caper.Logger
import Caper.Exceptions
import Caper.DeductionFailure
import Caper.ProverStates
import Caper.Guards
import Caper.Transitions
import qualified Caper.TypingContext as TC

data RegionInstance = RegionInstance {
        riType :: RTId,
        riParameters :: [Expr VariableID]  -- EXCLUDING region identifier
}

data Region = Region {
        regDirty :: Bool,
        regTypeInstance :: Maybe RegionInstance,
        regState :: Maybe (ValueExpression VariableID),
        regGuards :: Guard VariableID
}

data OpenRegion = OpenRegion {
        oregID :: VariableID,
        oregInitialState :: ValueExpression VariableID,
        oregInitialGuard :: Guard VariableID,
        oregType :: RegionType,
        oregParams :: [Expr VariableID],
        oregParamLVars :: LVarBindings
        }

class RegionLenses a where
        regions :: Simple Lens a (AliasMap VariableID Region)
        openRegions :: Simple Lens a [OpenRegion]
        

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
mergeRegionInstances :: (MonadState s m, AssumptionLenses s, MonadDemonic m) => RegionInstance -> RegionInstance -> m RegionInstance
mergeRegionInstances i1@(RegionInstance t1 ps1) i2@(RegionInstance t2 ps2)
        = (if t1 /= t2 then
                -- These regions cannot be the same, so assume false!
                -- assumeContradiction
                succeed
          else forM_ (zip ps1 ps2) $ \(p1, p2) ->
                        -- The precondition should guarantee against an error
                        -- in exprEquality.
                        assume $ exprEquality p1 p2)
          >> return i1

mergeValueExpressions :: (MonadState s m, AssumptionLenses s) =>
        ValueExpression VariableID ->
        ValueExpression VariableID -> m (ValueExpression VariableID)
mergeValueExpressions ve1 ve2 = assumeTrue (ve1 $=$ ve2) >> return ve1

mergeRegions :: (MonadState s m, AssumptionLenses s, MonadReader r m, RTCGetter r, MonadDemonic m, DebugState s r, MonadLabel CapturedState m) =>
        Region -> Region -> m Region
mergeRegions r1 r2 = do
                let dirty = regDirty r1 || regDirty r2
                ti <- mergeMaybe mergeRegionInstances (regTypeInstance r1) (regTypeInstance r2)
                s <- mergeMaybe mergeValueExpressions (regState r1) (regState r2)
                g <- mergeGuards (regGuards r1) (regGuards r2)
                case ti of
                        (Just (RegionInstance rtid _)) -> do
                                res <- view resolveRType
                                strongCheckGuardAtTLType g (rtGuardType (res rtid))
                        _ -> return ()
                return $ Region dirty ti s g

-- FIXME: Add bound information!
-- | Add a region, or merge it if one already exists with the same identifier.
-- Performs case analysis on whether the region is the same as an existing one.
--
-- Pre: the number and type of arguments should have been checked (otherwise an error may arise).
produceMergeRegion :: (MonadState s m, AssumptionLenses s, RegionLenses s,
                MonadReader r m, RTCGetter r, DebugState s r,
                MonadDemonic m, MonadLabel CapturedState m) =>
                VariableID -> Region -> m ()
produceMergeRegion rvar region = do
                regs <- use regions
                let rs = AM.toRootList regs
                --liftIO $ putStrLn $ "MERGEABLES: " ++ show (map fst rs)
                case AM.lookup rvar regs of
                        Nothing -> (do
                                --liftIO $ putStrLn $ "NOT MERGE " ++ show rvar
                                labelS $ "region " ++ show rvar ++ " is fresh"
                                regions .= AM.insert rvar region regs
                                forM_ rs (assume . DisequalityCondition rvar . fst)
                                _ <- runMaybeT $ do
                                    (RegionInstance rtid args) <- chooseFrom $ regTypeInstance region
                                    rt <- lookupRType rtid
                                    dc <- chooseFrom $ rtDistinctionCondition rt
                                    forM_ rs $ \(_, rg) -> runMaybeT $ do
                                        (RegionInstance rtid' args') <- chooseFrom $ regTypeInstance rg
                                        when (rtid == rtid') $ mapM_ assume $ dc args args'
                                return ()       
                                ) <#>
                            dAll [(do
                                --liftIO $ putStrLn $ "TRY MERGE: " ++ show rvar ++ ", " ++ show rid
                                assume $ EqualityCondition rvar rid
                                r' <- mergeRegions r region
                                regions .= (AM.addAlias rvar rid) (AM.overwrite rid r' regs)
                                labelS $ "region " ++ show rvar ++ " is " ++ show rid
                                --liftIO $ putStrLn $ "MERGED"
                                ) | (rid, r) <- rs]
                        (Just r) -> do
                                r' <- mergeRegions r region
                                regions .= AM.overwrite rvar r' regs


-- XXX: This is overkill.  In all but very few cases the rid should already
-- point to a region.
consumeRegion :: (MonadState s m, AssertionLenses s, RegionLenses s,
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
                
-- TODO: Put somewhere more appropriate?
restoring :: (MonadState s m) => m a -> m a
-- ^Run a stateful computation, restoring the state at the beginning.
restoring f = do
            s <- get
            r <- f
            put s
            return r 
                   
-- |Determine if two variables cannot be aliases for the same region.
-- In the current representation, Caper case splits on whether regions
-- are aliases, so this returns `True` exactly when the regions are not
-- considered to be aliased.
cannotAlias :: (ProverM s r m, RegionLenses s) => VariableID -> VariableID -> m Bool
cannotAlias r1 r2 = use regions >>= return . not . AM.areAliases r1 r2

-- |Stabilise all regions
stabiliseRegions :: (ProverM s r m, RegionLenses s, RTCGetter r, DebugState s r, MonadRaise m, MonadLabel CapturedState m) =>
                        m ()
stabiliseRegions = do
                        regs <- use regions
                        regs' <- imapM stabiliseRegion regs
                        regions .= regs'

-- |Stabilise a region.
stabiliseRegion :: (ProverM s r m, RTCGetter r, DebugState s r, MonadRaise m, MonadLabel CapturedState m) =>
                        VariableID -> Region -> m Region
-- Not dirty, so nothing to do!
stabiliseRegion rid
        reg@(Region False _ _ _) = return reg
-- Here we know enough about the region that we have to do something
stabiliseRegion rid
        (Region _ rti@(Just (RegionInstance rtid ps0)) (Just se) gd) = do
                        let ps = var rid : ps0
                        -- resolve region type
                        rt <- lookupRType rtid
                        transitions <- checkTransitions rt ps gd
                        -- compute the closure relation
                        tcrel <- rely rt transitions
                        -- create a new state variable
                        newStateVar <- newAvar "state"
                        -- assume it is related to the old state
                        assumeTrue $ tcrel se (var newStateVar)
                        labelS $ "Stabilising region " ++ show rid ++ " with Rely: " ++ show (tcrel se (var newStateVar))
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
stabiliseRegion rid r = return $ r {regDirty = False, regState = Nothing}

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
                        let bvars = Map.elems bvmap
                        let subst = Map.union params $ fmap var bvmap
                        let s v = Map.findWithDefault (error $ "checkTransitions: variable not found: " ++ show v ++ " in " ++ show (Map.toList subst)) v subst
                        -- Now have to check if guard is applicable!
                        guardCompat <- hypothetical $ do
                                -- assume conditions
                                mapM_ (assume . exprCASub' s) prd
                                -- combine guards
                                gd' <- mergeGuards gd (exprCASub' s trgd)
                                -- We extract the assumptions that condition the transition.
                                -- Currently, this takes all assumptions that involve value variables
                                -- that are in the transition.  We can only take conditions that
                                -- are value-convertible (since they will form part of a rely relation).
                                -- Previously, we only considered conditions with variables occurring in
                                -- the pre- or post-state.  However, this is restrictive when we have
                                -- other variables that are related to these variables and are themselves
                                -- conditioned.  This new version may be overly inclusive (i.e. include
                                -- conditions that are universally true).  This is probably not a big
                                -- problem.
                                assms <- use assumptions
                                bndgs <- use bindings
                                let cvars = [v | v <- Map.elems bvmap, TC.lookup v bndgs == TC.JustType VTValue]
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
                            let cond = foldBy FOFAnd FOFTrue $ valueConditions (const True) cassms
                            return [GuardedTransition bvars cond (exprSub s prec) (exprSub s post)]

-- |Determine a list of possible thread (guarantee) transitions for a given
-- parametrised region type and guard.
checkGuaranteeTransitions :: (ProverM (WithAssertions s) r m, AssumptionLenses s, DebugState (WithAssertions s) r, MonadRaise m) =>
        RegionType -> [Expr VariableID] -> Guard VariableID -> m [GuardedTransition VariableID]
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
                                justCheck
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


-- |Generate a 'Condition' that captures the fact that two abstract
-- states must be related by the guarantee for a region.   
generateGuaranteeCondition :: (ProverM (WithAssertions s) r m, AssumptionLenses s, DebugState (WithAssertions s) r, MonadRaise m, MonadLabel CapturedState m) =>
    RegionType                      -- ^Type of the region
    -> [Expr VariableID]            -- ^Parameters for the region
    -> Guard VariableID             -- ^Guard for the region
    -> ValueExpression VariableID   -- ^Old state
    -> ValueExpression VariableID   -- ^New state
        -> m (Condition VariableID)
generateGuaranteeCondition rt params gd st0 st1
    | not (isFinite (rtStateSpace rt)) = do
        transitions <- checkGuaranteeTransitions rt params gd
        return $ ValueCondition $ foldl FOFOr (st0 $=$ st1) $ do
            GuardedTransition bvars cond e0 e1 <- transitions
            let c = FOFAnd (FOFAnd (st0 $=$ e0) (st1 $=$ e1)) cond
            return $ foldr FOFExists c bvars
    | otherwise = do
        transitions <- checkGuaranteeTransitions rt params gd
        rel <- underComputeClosureRelation (rtStateSpace rt) transitions
        return $ ValueCondition (rel st0 st1)


