{-# LANGUAGE RankNTypes, BangPatterns, MultiParamTypeClasses, FlexibleContexts #-}
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
import Text.ParserCombinators.Parsec (SourcePos)

import Caper.Utils.SimilarStrings
import Caper.Utils.NondetClasses
import Caper.Utils.Alternating

import Caper.FreeVariables
import Caper.Guards
import Caper.ProverDatatypes
import Caper.ProverStates
import Caper.Prover
import Caper.Exceptions
import Caper.Logger
import qualified Caper.Parser.AST as AST
import Caper.Parser.AST.Annotation ()
import Caper.DeclarationTyping
import Caper.Assertions.Generate
import Caper.ExceptionContext

-- The internal representation of a region type identifier
type RTId = Integer

-- Variables for use with region type declarations
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

data RegionType = RegionType
        {
                rtSourcePos :: SourcePos,
                rtRegionTypeName :: String,
                rtParameters :: [(RTDVar, VariableType)],
                rtGuardType :: AST.TopLevelGuardDeclr,
                rtStateSpace :: StateSpace,
                rtTransitionSystem :: [TransitionRule],
                rtIsTransitive :: Bool,
                rtInterpretation :: [AST.StateInterpretation]
        }

instance Contextual RegionType where
        toContext rt = DescriptiveContext (rtSourcePos rt) $
                "In a region type declaration named '" ++ rtRegionTypeName rt ++ "'"

instance Show RegionType where
        show (RegionType _ nm params gt ss ts _ interp) =
                "region " ++ nm ++ "(" ++ intercalate "," (map (show . fst) params) ++ ") {\n" ++
                "  guards : " ++ show gt ++ "\n" ++
                "  transitions {\n    " ++ intercalate "\n    " (map show ts) ++ "\n  }\n" ++
                "}"

rtWeakGT :: RegionType -> WeakGuardType
rtWeakGT = topLevelToWeakGuardType . rtGuardType

rtParamVars :: RegionType -> Set RTDVar
rtParamVars = Set.fromList . map fst . rtParameters

rtParamNames :: RegionType -> [String]
-- ^Get a the list of parameter names for the region type.
rtParamNames = map (rtdvStr . fst) . rtParameters

rtFullGuard :: RegionType -> Guard VariableID
rtFullGuard = fullGuard . rtWeakGT

-- StateSpace

-- ssLowerBound and ssUpperBound are the (inclusive) lower
-- and upper bounds of the state space.
-- invariant: ssLowerBound <= ssUpperBound (if both are not Nothing)
data StateSpace = StateSpace {
                ssLowerBound :: Maybe Int,
                ssUpperBound :: Maybe Int
                } deriving (Eq,Ord)

instance Show StateSpace where
        show (StateSpace a b) = "[" ++ maybe "?" show a ++ "-" ++ maybe "?" show b ++ "]"

isFinite :: StateSpace -> Bool
isFinite (StateSpace (Just _) (Just _)) = True
isFinite _ = False

ssSize :: (MonadPlus m) => StateSpace -> m Int
ssSize (StateSpace (Just x) (Just y)) = return $ y - x + 1
ssSize _ = mzero



data TransitionRule = TransitionRule
        {
                -- The guard that is required to perform the transition
                trGuard :: Guard RTDVar,
                -- Some (pure) predicate that conditions the transition
                trPredicate :: [Condition RTDVar],
                -- An expression describing the state to transition from
                trPreState :: ValueExpression RTDVar,
                -- An expression describing the state to transition to
                trPostState :: ValueExpression RTDVar
        }

instance Show TransitionRule where
        show (TransitionRule gd prd prec post) =
                show prd ++ " | " ++ show gd ++ " : " ++ show prec ++ " ~> " ++ show post

instance FreeVariables TransitionRule RTDVar where
    foldrFree f b tr = foldr f (foldr f (foldrFree f (foldrFree f b (trGuard tr)) (trPredicate tr)) (trPreState tr)) (trPostState tr) 

varExprToRTDVar :: (Monad m) => AST.VarExpr -> StateT [RTDVar] m RTDVar
varExprToRTDVar (AST.Variable _ s) = return (RTDVar s)
varExprToRTDVar (AST.WildCard _) = state (head &&& tail)

actionToTransitionRule :: (MonadRaise m, Monad m) => [RTDVar] -> AST.Action -> m TransitionRule
actionToTransitionRule params act@(AST.Action _ conds gds prest postst) =
        contextualise act $ do
            -- unless (null conds) $ raise $ SyntaxNotImplemented "predicated transitions"
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
        -- nextFresh = state (head &&& tail)
        -- For each permission guard, generate a condition that the permission is non-zero
        pehandler pe = modify (negativeCondition (PAEq pe PEZero) :)
        pedisj pe1 pe2 = modify (toCondition (PADis pe1 pe2) :)

data RegionTypeContext = RegionTypeContext
        {
                rtcIds :: Map String RTId,
                rtcRegionTypes :: Map RTId RegionType
        }
instance Show RegionTypeContext where
    show (RegionTypeContext ids rts) = Map.foldWithKey showRegion "" ids
        where
            showRegion rname rid rest = rname ++ ": " ++ show (Map.lookup rid rts) ++ "\n"

-- |The region type context with no region types.
emptyRegionTypeContext :: RegionTypeContext
emptyRegionTypeContext = RegionTypeContext Map.empty Map.empty

class RTCGetter a where
        theRTContext :: Getter a RegionTypeContext
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
        theRTContext = to id

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
        -> m RegionTypeContext
declrsToRegionTypeContext declrs = do
            -- Determine the parameter types for (region) declarations
            typings <- typeDeclarations declrs
            -- Build the region type context
            accumulate typings 0 emptyRegionTypeContext (AST.regionDeclrs declrs)
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
                    let rt0 = RegionType sp rtnam params gddec stateSpace transitions False interps
                    isTrans <- isTransitive rt0
                    let rt = rt0 { rtIsTransitive = isTrans }
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

checkForClosure :: (MonadIO m, MonadPlus m, MonadLogger m, MonadReader r m, Provers r) =>
        RegionType -> TransitionRule -> TransitionRule -> m ()
checkForClosure rt tr1 tr2 = flip evalStateT emptyAssumptions $ do
        -- Generate parameters for the region
        pmap <- liftM Map.fromList $ forM (rtParameters rt) $ \(param, ptype) -> do
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
            grd <- conservativeGuardLUBTL (rtGuardType rt)
                    (exprCASub' (sub pmap1) (trGuard tr1)) (exprCASub' (sub pmap2) (trGuard tr2))
            -- Try to find a third transition that subsumes the sequencing.
            msum $ flip map (rtTransitionSystem rt) $ \tr3 -> check $ do
                pmap3 <- transParams newEvar pmap tr3
                mapM_ (assert . exprCASub' (sub pmap3)) (trPredicate tr3)
                _ <- guardEntailmentTL (rtGuardType rt) grd (exprCASub' (sub pmap3) (trGuard tr3))
                assertTrue $ exprSub (sub pmap1) (trPreState tr1) $=$ exprSub (sub pmap3) (trPreState tr3)
                assertTrue $ exprSub (sub pmap2) (trPostState tr2) $=$ exprSub (sub pmap3) (trPostState tr3)
    where
        transParams new = foldrFreeM (transParam new)
        transParam new param pmap = if param `Map.member` pmap then return pmap else do
                        v <- new (varToString param)
                        return $ Map.insert param v pmap
        sub :: Map.Map RTDVar VariableID -> RTDVar -> Expr VariableID
        sub pmap v = toExpr $ Identity $ Map.findWithDefault (error "checkForClosure: variable not found") v pmap 
