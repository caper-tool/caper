{- Regions -}
module Caper.Regions where
import Prelude hiding (mapM_,mapM,concat)
import Control.Monad.State hiding (mapM_,mapM,forM_,msum)
import Control.Monad.Reader hiding (mapM_,mapM,forM_,msum)
import Control.Lens hiding (op)
import Data.Foldable
import Data.Traversable
import qualified Data.Map as Map
import qualified Data.Set as Set

import Caper.Utils.Choice
import Caper.RegionTypes
import Caper.Utils.AliasingMap (AliasMap)
import qualified Caper.Utils.AliasingMap as AM
import Caper.Logger
import Caper.ProverDatatypes
import Caper.Prover -- TODO: move some stuff from Prover to ProverDatatypes?
import Caper.Guards
import Caper.Transitions


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

newtype Regions = Regions {_regions :: AliasMap VariableID Region}

class RegionLenses a where
        regions :: Simple Lens a (AliasMap VariableID Region)

instance RegionLenses Regions where
        regions = lens _regions (\_ y -> Regions y)

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
                                regions .= AM.insert rvar r' regs


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
                

-- Stabilise all regions
stabiliseRegions :: (ProverM s r m, RegionLenses s, RTCGetter r) =>
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
stabiliseRegion :: (ProverM s r m, RTCGetter r) =>
                        Region -> m Region
-- Not dirty, so nothing to do!
stabiliseRegion
        reg@(Region False _ _ _) = return reg
-- Here we know enough about the region that we have to do something
stabiliseRegion
        (Region _ rti@(Just (RegionInstance rtid ps)) (Just se) gd) = do
                        -- resolve region type
                        rt <- lookupRType rtid
                        transitions <- checkTransitions rt ps gd
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


checkTransitions :: (ProverM s r m) => RegionType -> [Expr VariableID] -> Guard VariableID -> m [GuardedTransition VariableID]
checkTransitions rt ps gd = liftM concat $ mapM checkTrans (rtTransitionSystem rt)
        where
                boundVars tr = Set.difference (trVariables tr) (rtParamVars rt)
                params = Map.fromList $ zip (map fst $ rtParameters rt) ps
                checkTrans tr@(TransitionRule trgd pred pre post) = do
                        -- Compute a binding for fresh variables
                        bvmap <- freshInternals rtdvStr (boundVars tr)
                        let bvars = Map.elems bvmap
                        let subst = Map.union params $ fmap var bvmap
                        let s v = Map.findWithDefault (error "checkTransitions: variable not found") v subst
                        -- Now have to check if guard is applicable!
                        guardCompat <- hypothetical $ do
                                -- combine guards
                                gd' <- mergeGuards gd (exprSub s trgd)
                                -- check the matches the guard type
                                if checkGuardAtType gd' (topLevelToWeakGuardType $ rtGuardType rt) then
                                        -- and is consistent
                                        isConsistent
                                    else
                                        return $ Just False
                        return $ if guardCompat == Just False then [] else
                                [GuardedTransition bvars FOFTrue (exprSub s pre) (exprSub s post)]


subVars' :: (Traversable t, ExpressionSub t e, Expression e) =>
        (String -> VariableID) -> RegionType -> [e VariableID] -> t RTDVar -> t VariableID
subVars' frsh rt ps = exprSub s
        where
                s v@(RTDVar vn) = Map.findWithDefault (var $ frsh vn) v params
                params = Map.fromList $ zip (map fst $ rtParameters rt) ps

subVars :: (ProverM s r m, Traversable t, ExpressionSub t e, Expression e) =>
        RegionType -> [e VariableID] -> t RTDVar -> m (t VariableID)
subVars rt ps o = do
                -- determine the substitution
                subs <- foldrM makeSubs params o
                let s v = Map.findWithDefault (error "subVars: variable not found") v subs
                -- apply the substitution
                return $ exprSub s o
        where
                makeSubs vr@(RTDVar vn) mp =
                        -- determine substitution
                        case Map.lookup vr params of
                                (Just e) -> return mp
                                Nothing -> do
                                        mt <- liftM var $ freshInternal vn
                                        return $ Map.insert vr mt mp
                --params :: Map.Map RTDVar (e VariableID)
                params = Map.fromList $ zip (map fst $ rtParameters rt) ps


-- Check if a guard is compatible 
