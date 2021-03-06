{-# LANGUAGE RankNTypes, BangPatterns, MultiParamTypeClasses, FlexibleContexts, DeriveFunctor, DeriveFoldable, FlexibleInstances #-}
module Caper.RegionTypes where

import Prelude hiding (notElem, mapM_, foldr)
import Control.Monad hiding (mapM_, msum)
import Control.Monad.Reader.Class
import Control.Monad.State hiding (mapM_, msum)
import Control.Arrow
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Foldable
import Control.Lens
import Data.Maybe
import Data.List (intercalate)
import Data.IntCast
import Data.Tuple (swap)
import Text.ParserCombinators.Parsec (SourcePos)

import Caper.Utils.SimilarStrings
import Caper.Utils.NondetClasses
import Caper.Utils.Alternating

import Caper.Constants (closureDepth)
import Caper.FreeVariables
import Caper.Guards
import Caper.ProverStates
import Caper.Exceptions
import Caper.Logger
import qualified Caper.Parser.AST as AST
import Caper.Parser.AST.Annotation ()
-- import Caper.DeclarationTyping
import Caper.Assertions.Generate
-- import Caper.ExceptionContext

-- |The internal representation of a region type identifier
type RTId = Integer

-- |Variables for use with region type declarations
-- There will be a few different binding locations, including
-- top level
newtype RTDVar = RTDVar { rtdvStr :: String } deriving (Eq,Ord)
instance Show RTDVar where
        show (RTDVar s) = s
instance StringVariable RTDVar where
        varToString (RTDVar s) = s
        varFromString = RTDVar
instance Refreshable RTDVar where
        freshen (RTDVar s) = map RTDVar (freshen s) 

-- |Internal representation of a region type.
data RegionType = RegionType
        {
                -- |Source of the definition.
                rtSourcePos :: SourcePos,
                -- |Name of the region type
                rtRegionTypeName :: String,
                -- |The typed parameters of the region, INCLUDING the region identifier
                rtParameters :: [(RTDVar, VariableType)],
                -- |The guard delcaration
                rtGuardType :: AST.TopLevelGuardDeclr,
                -- |Bounds on the state space
                rtStateSpace :: StateSpace,
                -- |The transition system as a list of transition rules
                rtTransitionSystem :: [TransitionRule],
                -- |Flag indicating whether the transition system is transitively closed
                rtIsTransitive :: Bool,
                -- |State interpretation
                rtInterpretation :: [AST.StateInterpretation],
                -- |An optional function that generates side conditions for two regions being distinct
                rtDistinctionCondition :: (Maybe ([Expr VariableID] -> [Expr VariableID] -> [Condition VariableID]))
        }

instance Contextual RegionType where
        toContext rt = DescriptiveContext (rtSourcePos rt) $
                "In a region type declaration named '" ++ rtRegionTypeName rt ++ "'"

instance Show RegionType where
        show (RegionType _ nm params gt ss ts ttv interp _) =
                "region " ++ nm ++ "(" ++ intercalate "," (map (show . fst) params) ++ ") {\n" ++
                "  guards : " ++ show gt ++ "\n" ++
                "  transitions {\n    " ++ intercalate "\n    " (map show ts) ++ "\n  }\n" ++
                (if ttv then "  #Transitive\n" else "  #NotTransitive\n") ++
                "}"

rtWeakGT :: RegionType -> WeakGuardType
-- ^The weak guard type for the region type.
rtWeakGT = topLevelToWeakGuardType . rtGuardType

rtParamVars :: RegionType -> Set RTDVar
-- ^The parameters for the region type (including region identifier).
rtParamVars = Set.fromList . map fst . rtParameters

rtParamNames :: RegionType -> [String]
-- ^Get a the list of parameter names for the region type.
rtParamNames = map (rtdvStr . fst) . rtParameters

rtFullGuard :: RegionType -> Guard VariableID
-- ^The (or a) full guard for the region type.
rtFullGuard = fullGuard . rtWeakGT

-- |Representation of the state space of a region type.
-- ssLowerBound and ssUpperBound are the (inclusive) lower
-- and upper bounds of the state space.
-- invariant: @ssLowerBound <= ssUpperBound@ (if both are not Nothing)
data StateSpace = StateSpace {
                -- |Optional lower bound
                ssLowerBound :: Maybe Int,
                -- |Optional upper bound
                ssUpperBound :: Maybe Int
                } deriving (Eq,Ord)

instance Show StateSpace where
        show (StateSpace a b) = "[" ++ maybe "?" show a ++ "-" ++ maybe "?" show b ++ "]"

-- |Determine if a state space is finitely bounded.
isFinite :: StateSpace -> Bool
isFinite (StateSpace (Just _) (Just _)) = True
isFinite _ = False

-- |Internal representation of a transition rule (action).
-- The definition is parametrised by the type of variables as a convenience
-- for deriving folds.
data GeneralTransitionRule v = TransitionRule
        {
                -- |The guard that is required to perform the transition
                trGuard :: Guard v,
                -- |Some (pure) predicate that conditions the transition
                trPredicate :: [Condition v],
                -- |An expression describing the state to transition from
                trPreState :: ValueExpression v,
                -- |An expression describing the state to transition to
                trPostState :: ValueExpression v
        } deriving (Functor, Foldable)

type TransitionRule = GeneralTransitionRule RTDVar

instance (Show a) => Show (GeneralTransitionRule a) where
        show (TransitionRule gd prd prec post) =
                show prd ++ " | " ++ show gd ++ " : " ++ show prec ++ " ~> " ++ show post

instance FreeVariables (GeneralTransitionRule a) a where
    foldrFree f b tr = foldr f (foldr f (foldrFree f (foldrFree f b (trGuard tr)) (trPredicate tr)) (trPreState tr)) (trPostState tr) 


varExprToRTDVar :: (Monad m) => AST.VarExpr -> StateT [RTDVar] m RTDVar
varExprToRTDVar (AST.Variable _ s) = return (RTDVar s)
varExprToRTDVar (AST.WildCard _) = state (head &&& tail)

-- |Convert the AST representation of an action to the internal representation
-- as a transition rule.
actionToTransitionRule :: (MonadRaise m, Monad m) => [RTDVar] -> AST.Action -> m TransitionRule
actionToTransitionRule params act@(AST.Action _ conds gds prest postst) =
        contextualise act $ do
            (cds, gg, prec, post) <- flip evalStateT freshVars $ do
                cds0 <- mapM (generatePure varExprToRTDVar) conds
                (gg, cds) <- runStateT (generateGuard (lift . varExprToRTDVar) (modify . (:)) gds) cds0
                prec <- generateValueExpr varExprToRTDVar prest
                post <- generateValueExpr varExprToRTDVar postst
                return (cds, gg,prec,post) 
            return $ TransitionRule gg cds prec post
    where
        theVars = params ++ (map RTDVar . mapMaybe AST.unVarExpr . Set.toList . freeVariables) act
        freshVars = filter (`notElem` theVars) [RTDVar ("WILDCARD" ++ show x) | x <- [(0::Int)..]]

data RegionTypeContext = RegionTypeContext
        {
                rtcIds :: Map String RTId,
                rtcRegionTypes :: Map RTId RegionType
        }
instance Show RegionTypeContext where
    show (RegionTypeContext ids rts) = Map.foldWithKey showRegion "" ids
        where
            showRegion rname rid rest = rname ++ ": " ++ show (Map.lookup rid rts) ++ "\n" ++ rest

-- |The region type context with no region types.
emptyRegionTypeContext :: RegionTypeContext
emptyRegionTypeContext = RegionTypeContext Map.empty Map.empty

class RTCGetter a where
        theRTContext :: Simple Lens a RegionTypeContext
        resolveRTName :: Getter a (String -> Maybe RTId)
        resolveRTName = to $ \c s -> Map.lookup s (rtcIds (c ^. theRTContext))
        resolveRType :: Getter a (RTId -> RegionType)
        resolveRType = to $ \c s -> fromMaybe
                        (resError s)
                        (Map.lookup s (rtcRegionTypes (c ^. theRTContext)))
                where
                        resError s = error $ "The region identifier " ++ show s ++ " could not be resolved."
lookupRType :: (MonadReader r m, RTCGetter r) => RTId -> m RegionType
lookupRType rtid = view resolveRType `ap` return rtid

lookupRTName :: (RTCGetter a) => String -> Getter a (Maybe RTId)
lookupRTName s = to $ \c -> Map.lookup s (rtcIds (c ^. theRTContext))

regionTypeNames :: (RTCGetter a) => Getter a [String]
regionTypeNames = to $ \c -> map fst (Map.toList (rtcIds (c ^. theRTContext)))

lookupRTNameE :: (MonadReader r m, RTCGetter r, MonadRaise m) =>
        String -> m RTId
lookupRTNameE s = do
        rmp <- view (theRTContext . to rtcIds)
        case rmp ^. at s of
                Nothing -> do
                        let rtnames = map fst (Map.toList rmp)
                        raise $ UndeclaredRegionType s
                                (similarStrings s rtnames)
                (Just rtid) -> return rtid

instance RTCGetter RegionTypeContext where
        theRTContext = id

createRegionTypeContext :: [RegionType] -> RegionTypeContext
createRegionTypeContext = crtcs 0 emptyRegionTypeContext
        where
                crtcs nextRTId ac [] = ac
                crtcs nextRTId ac (r : rs) = crtcs (nextRTId + 1)
                        (ac { rtcIds = Map.insert (rtRegionTypeName r) nextRTId (rtcIds ac), rtcRegionTypes = Map.insert nextRTId r (rtcRegionTypes ac) })
                        rs

-- |Determine the 'StateSpace' for a region by examining the given state
-- interpretations.  Currently only finds bounds in the finite state case.
--
-- Precondition: the list of interpretations is non-empty
computeStateSpace :: [AST.StateInterpretation] -> StateSpace
computeStateSpace ss = case constStates ss Set.empty of
            Nothing -> StateSpace Nothing Nothing
            (Just s) -> StateSpace (Just $ Set.findMin s) (Just $ Set.findMax s)
        where
            constStates [] s = Just s
            constStates (x:xs) s = case x of
                 (AST.StateInterpretation _ _ (AST.ConstValExpr _ n) _) -> do
                    n' <- intCastMaybe n
                    constStates xs (Set.insert n' s)
                 (AST.StateInterpretation _ _ (AST.UnaryValExpr _ AST.ValNegation (AST.ConstValExpr _ n)) _) -> do
                    n' <- intCastMaybe n
                    constStates xs (Set.insert (-n') s)
                 _ -> Nothing

-- | Check that the guards for the action conform to the guard algebra 
checkActionsGuards :: (Monad m, MonadRaise m) =>
        AST.TopLevelGuardDeclr -> [AST.Action] -> m ()
checkActionsGuards tlgd@(AST.SomeGuardDeclr gd) = mapM_ $ \a -> let grd = AST.actionGuard a in
        contextualise a $ do            
            g <- generateGuard (const (return (RTDVar "x"))) (\_ -> return ()) grd
            unless (checkGuardAtType g (toWeakGuardType gd)) $
                raise $ GuardInconsistentWithGuardType (show grd) (show tlgd)
checkActionsGuards tlgd@AST.ZeroGuardDeclr = mapM_ $ \a -> let grd = AST.actionGuard a in
        contextualise a $            
            unless (null grd) $ raise $ GuardInconsistentWithGuardType (show grd) (show tlgd)

declrsToRegionTypeContext :: (MonadIO m, MonadRaise m, MonadLogger m, MonadReader r m, Provers r) =>
        [AST.Declr]
        -- ^ Declarations
        -> (Map String [(String, VariableType)])
        -- ^ Typing for region parameters
        -> m RegionTypeContext
declrsToRegionTypeContext declrs typings0 = do
            -- Build the region type context
            accumulate typings0 0 emptyRegionTypeContext (AST.regionDeclrs declrs)
    where
        accumulate typings nextRTId ac [] = return ac
        accumulate typings nextRTId ac
            (decl@(AST.RegionDeclr sp rtnam rtparams gddec interps acts):rs) =
                do
                    -- Look up the parameter types.  This should not fail.
                    let !params = map toParam $ Map.findWithDefault
                            (error "declrsToRegionTypeContext: region parameters not determined.")
                            rtnam typings
                    -- Check that the guard declaration is legal
                    validateGuardDeclr gddec
                    -- Check that the action guards conform to the guard algebra
                    checkActionsGuards gddec acts
                    -- Check that there is at least some state interpretation
                    contextualise decl $ when (null interps) $
                        raise MissingStateInterpretation
                    -- Compute the state space (we have just checked the
                    -- precondition for this)
                    let !stateSpace = computeStateSpace interps
                    transitions <- mapM (actionToTransitionRule (map fst params)) acts
                    let rt0 = RegionType sp rtnam params gddec stateSpace transitions False interps Nothing
                    rt <- case isFinite stateSpace of
                        True -> do
                                isTrans <- isTransitive rt0
                                return $ rt0 {rtIsTransitive = isTrans}
                        False -> attemptClosure rt0
                    accumulate typings (nextRTId + 1)
                        (ac {
                            rtcIds = Map.insert rtnam nextRTId (rtcIds ac),
                            rtcRegionTypes = Map.insert nextRTId rt (rtcRegionTypes ac)
                            }) rs
        toParam (s, vt) = (RTDVar s, vt)

isTransitive :: (MonadIO m, MonadLogger m, MonadReader r m, Provers r) =>
        RegionType -> m Bool
isTransitive rt = do 
            m <- runAlternatingT $ dAll [checkForClosure rt tr1 tr2 | tr1 <- rtTransitionSystem rt, tr2 <- rtTransitionSystem rt]
            liftIO $ putStrLn $ "Transitivity check " ++ show (isJust m) ++ " for region type " ++ show rt
            return (isJust m)

checkForClosure :: (MonadIO m, MonadPlus m, MonadOrElse m, MonadLogger m, MonadReader r m, Provers r, MonadLabel CapturedState m, MonadDemonic m) =>
        RegionType -> TransitionRule -> TransitionRule -> m ()
checkForClosure rt = checkForClosure' (rtParameters rt) (rtGuardType rt) (rtTransitionSystem rt)

checkForClosure' :: (MonadIO m, MonadPlus m, MonadOrElse m, MonadLogger m, MonadReader r m, Provers r, MonadLabel CapturedState m, MonadDemonic m) =>
        [(RTDVar,VariableType)] -> AST.TopLevelGuardDeclr -> [TransitionRule] -> TransitionRule -> TransitionRule -> m ()
checkForClosure' params gt trs tr1 tr2 = flip evalStateT emptyAssumptions $ do
        -- Generate parameters for the region
        pmap <- liftM Map.fromList $ forM params $ \(param, ptype) -> do
            v <- newAvar (varToString param)
            bindVarAs v ptype
            return (param, v)
        -- Generate the parameters for the transitions
        pmap1 <- transParams newAvar pmap tr1
        pmap2 <- transParams newAvar pmap tr2
        -- Assume that the conditions hold
        mapM_ (assume . exprCASub' (sub pmap1)) (trPredicate tr1)
        mapM_ (assume . exprCASub' (sub pmap2)) (trPredicate tr2)
        -- Assume that the post-state of tr1 is the pre-state of tr2
        assumeTrue $ exprSub (sub pmap1) (trPostState tr1) $=$ exprSub (sub pmap2) (trPreState tr2)
        -- If the assumptions are inconsistent then these transitions cannot happen in sequence
        -- so we are done.  
        whenConsistent $ do
            -- Otherwise, compute (conservatively) the upper bound of the two guards 
            grd <- conservativeGuardLUBTL gt
                    (exprCASub' (sub pmap1) (trGuard tr1)) (exprCASub' (sub pmap2) (trGuard tr2))
            -- Try to find a third transition that subsumes the sequencing.
            (msum $ flip map trs $ \tr3 -> checkNoAbduce $ do
                pmap3 <- transParams newEvar pmap tr3
                mapM_ (assert . exprCASub' (sub pmap3)) (trPredicate tr3)
                _ <- guardEntailmentTL gt grd (exprCASub' (sub pmap3) (trGuard tr3))
                assertTrue $ exprSub (sub pmap1) (trPreState tr1) $=$ exprSub (sub pmap3) (trPreState tr3)
                assertTrue $ exprSub (sub pmap2) (trPostState tr2) $=$ exprSub (sub pmap3) (trPostState tr3))
    where
        sub :: Map.Map RTDVar VariableID -> RTDVar -> Expr VariableID
        sub pmap v = toExpr $ Identity $ Map.findWithDefault (error "checkForClosure: variable not found") v pmap

-- TODO: This doesn't currently account for reflexivity.
notSubsumedBy :: (MonadIO m, MonadLogger m, MonadReader r m, Provers r) =>
        [(RTDVar,VariableType)] -- ^Region parameters
        -> AST.TopLevelGuardDeclr   -- ^Guard type
        -> TransitionRule
        -> TransitionRule
        -> m Bool
notSubsumedBy params gt tr1 tr2 = liftM isNothing $ runAlternatingT $ flip evalStateT emptyAssumptions $ do
        -- Generate parameters for the region
        pmap <- liftM Map.fromList $ forM params $ \(param, ptype) -> do
            v <- newAvar (varToString param)
            bindVarAs v ptype
            return (param, v)
        -- Generate the parameters for the first transition
        pmap1 <- transParams newAvar pmap tr1
        -- Assume that the conditions for the first transition hold
        mapM_ (assume . exprCASub' (sub pmap1)) (trPredicate tr1)
        checkNoAbduce $ do
                -- Generate the parameters for the second transition
                pmap2 <- transParams newEvar pmap tr2
                -- Assert that the conditions for the second transition hold
                mapM_ (assert . exprCASub' (sub pmap2)) (trPredicate tr2)
                -- Assert guard entailment
                _ <- guardEntailmentTL gt (exprCASub' (sub pmap1) (trGuard tr1)) (exprCASub' (sub pmap2) (trGuard tr2))
                -- Assert equality for the pre and post states
                assertTrue $ exprSub (sub pmap1) (trPreState tr1) $=$ exprSub (sub pmap2) (trPreState tr2)
                assertTrue $ exprSub (sub pmap1) (trPostState tr1) $=$ exprSub (sub pmap2) (trPostState tr2)
    where
        sub :: Map.Map RTDVar VariableID -> RTDVar -> Expr VariableID
        sub pmap v = toExpr $ Identity $ Map.findWithDefault (error "notSubsumedBy: variable not found") v pmap

transParams :: (StringVariable k, FreeVariables t k, Ord k, Monad m) =>
        (String -> m a) -> Map k a -> t -> m (Map k a)
transParams = foldrFreeM . transParam
        where
                transParam newVar param pmap = if param `Map.member` pmap then return pmap else do
                        v <- newVar (varToString param)
                        return $ Map.insert param v pmap

composeTransitions ::
        [(RTDVar,VariableType)] -> AST.TopLevelGuardDeclr -> TransitionRule -> TransitionRule -> TransitionRule
composeTransitions params gt tr1 tr2 = fixVars (TransitionRule grd cnd prestate poststate)
    where
        ((grd,prestate,poststate,pmapr),Assumptions{_assmAssumptions=cnd}) = flip runState emptyAssumptions $ do
                -- Generate parameters for the region
                pmaplst <- forM params $ \(param, ptype) -> do
                    v <- newAvar (varToString param)
                    bindVarAs v ptype
                    return (param, v)
                let pmap = Map.fromList pmaplst
                -- Generate the parameters for the transitions
                pmap1 <- transParams newAvar pmap tr1
                pmap2 <- transParams newAvar pmap tr2
                -- Assume that the conditions hold
                mapM_ (assume . exprCASub' (sub pmap1)) (trPredicate tr1)
                mapM_ (assume . exprCASub' (sub pmap2)) (trPredicate tr2)
                -- Assume that the post-state of tr1 is the pre-state of tr2
                assumeTrue $ exprSub (sub pmap1) (trPostState tr1) $=$ exprSub (sub pmap2) (trPreState tr2)
                -- Compute (conservatively) the upper bound of the two guards
                grd0 <- conservativeGuardLUBTL gt
                            (exprCASub' (sub pmap1) (trGuard tr1)) (exprCASub' (sub pmap2) (trGuard tr2))
                return (grd0,
                        exprSub (sub pmap1) (trPreState tr1),
                        exprSub (sub pmap2) (trPostState tr2),
                        Map.fromList (map swap pmaplst))
        sub :: Map.Map RTDVar VariableID -> RTDVar -> Expr VariableID
        sub pmap v = toExpr $ Identity $ Map.findWithDefault (error "composeTransitions: variable not found") v pmap
        fixVars = refreshLefts frshv . fmap (\x -> maybe (Left x) Right (Map.lookup x pmapr))
        frshv (VIDNamed s) = nearFreshen (RTDVar s) 
        frshv (VIDInternal s) = nearFreshen (RTDVar s)
        frshv (VIDExistential s) = nearFreshen (RTDVar s)

generateComposedTransitions :: (MonadIO m, MonadLogger m, MonadReader r m, Provers r) =>
        [(RTDVar,VariableType)] -- ^Region parameters
        -> AST.TopLevelGuardDeclr   -- ^Guard type
        -> [TransitionRule]     -- ^Old transitions
        -> [TransitionRule]     -- ^New transitions
        -> m ([TransitionRule], [TransitionRule])
generateComposedTransitions params gt oldtrs0 newtrs0 = foldM genOne (oldtrs0 ++ newtrs0, []) trPairs
        where
                trPairs = [(tr1,tr2) | tr1 <- oldtrs0 ++ newtrs0, tr2 <- newtrs0] ++ [(tr1,tr2) | tr1 <- newtrs0, tr2 <- oldtrs0]
                genOne (oldtrs, newtrs) (tr1, tr2) = do
                        m <- runAlternatingT $ checkForClosure' params gt (oldtrs ++ newtrs) tr1 tr2
                        case m of
                                Just _ -> return (oldtrs, newtrs)
                                Nothing -> do
                                        logEvent (InfoEvent $ "Transitivity check failed for actions:\n  " ++ show tr1 ++ "\n  " ++ show tr2)
                                        let tr' = composeTransitions params gt tr1 tr2
                                        let notSub x = do
                                                res <- notSubsumedBy params gt x tr'
                                                unless res $ logEvent $ InfoEvent $ "Action\n  " ++ show x ++ "\nis subsumed by\n  " ++ show tr'
                                                return res
                                        oldtrs' <- filterM notSub oldtrs
                                        newtrs' <- filterM notSub newtrs
                                        return (oldtrs', tr' : newtrs')

attemptClosure :: (MonadIO m, MonadLogger m, MonadReader r m, Provers r) =>
        RegionType -> m RegionType
attemptClosure rt@(RegionType{rtParameters = params, rtGuardType = gt, rtTransitionSystem = trs0}) = ac closureDepth [] trs0
        where
                ac n oldtrs [] = do
                                    logEvent $ InfoEvent $ "Region type " ++ rtRegionTypeName rt ++ " is transitively closed with actions:\n  " ++ intercalate "\n  " (map show oldtrs)
                                    return rt{rtTransitionSystem = oldtrs, rtIsTransitive = True}
                ac n oldtrs newtrs
                        | n <= 0 = do
                                    logEvent $ WarnNontransitiveRegionType $ rtRegionTypeName rt
                                    return rt{rtIsTransitive = False}
                        | otherwise = do
                                (oldtrs', newtrs') <- generateComposedTransitions params gt oldtrs newtrs
                                ac (n - 1) oldtrs' newtrs'

addComposedTransitions :: (MonadIO m, MonadLogger m, MonadReader r m, Provers r) =>
        RegionType -> m (RegionType, Bool)
addComposedTransitions rt0 = foldM addOne (rt0,True) [(tr1,tr2)| tr1 <- rtTransitionSystem rt0, tr2 <- rtTransitionSystem rt0]
        where
                addOne (rt,closedSoFar) (tr1, tr2) = do
                        m <- runAlternatingT $ checkForClosure rt tr1 tr2
                        case m of
                                Just _ -> return (rt,closedSoFar)
                                Nothing -> return (rt{rtTransitionSystem = composeTransitions (rtParameters rt) (rtGuardType rt) tr1 tr2 : rtTransitionSystem rt},False)

iterateAddTransitions :: (MonadIO m, MonadLogger m, MonadReader r m, Provers r) =>
        Int -> RegionType -> m RegionType
iterateAddTransitions n rt
        | n > 0 = do
                        (rt', b) <- addComposedTransitions rt
                        if b then return rt' else iterateAddTransitions (n-1) rt'
        | otherwise = return rt

