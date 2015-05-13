{-# LANGUAGE RankNTypes, BangPatterns, MultiParamTypeClasses #-}
module Caper.RegionTypes where
import Control.Monad
import Control.Monad.Reader.Class
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Foldable
import Control.Lens
import Data.Maybe
import Data.List (intercalate)
import Data.IntCast

import Caper.Utils.SimilarStrings
import Caper.Guards
import Caper.ProverDatatypes
import Caper.Exceptions
import Caper.Logger
import qualified Caper.Parser.AST as AST
import Caper.Parser.AST.Annotation ()
import Caper.DeclarationTyping

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


data RegionType = RegionType
        {
                rtRegionTypeName :: String,
                rtParameters :: [(RTDVar, VariableType)],
                rtGuardType :: AST.TopLevelGuardDeclr,
                rtStateSpace :: StateSpace,
                rtTransitionSystem :: [TransitionRule],
                rtInterpretation :: [AST.StateInterpretation]
        }

instance Show RegionType where
        show (RegionType nm params gt ss ts interp) =
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

-- StateSpace

-- ssLowerBound and ssUpperBound are the (inclusive) lower
-- and upper bounds of the state space.
-- invariant: ssLowerBound <= ssUpperBound (if both are not Nothing)
data StateSpace = StateSpace {
                ssLowerBound :: Maybe Int,
                ssUpperBound :: Maybe Int
                }

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
                -- (Not Implemented Yet)
                trPredicate :: (),
                -- An expression describing the state to transition from
                trPreState :: ValueExpression RTDVar,
                -- An expression describing the state to transition to
                trPostState :: ValueExpression RTDVar
        }

trVariables :: TransitionRule -> Set RTDVar
trVariables (TransitionRule g prd prec post) = Set.fromList $ toList g ++ toList prec ++ toList post

instance Show TransitionRule where
        show (TransitionRule gd prd prec post) =
                show gd ++ " : " ++ show prec ++ " ~> " ++ show post

actionToTransitionRule :: (MonadRaise m, Monad m) => AST.Action -> m TransitionRule
actionToTransitionRule act@(AST.Action _ conds gds prest postst) =
        contextualise act $ do
            unless (null conds) $ raise $ SyntaxNotImplemented "predicated transitions"
            -- generateGuards 
            return $ undefined TransitionRule
            -- TODO: this


data RegionTypeContext = RegionTypeContext
        {
                rtcIds :: Map String RTId,
                rtcRegionTypes :: Map RTId RegionType
        }

-- |The region type context with no region types.
emptyRegionTypeContext :: RegionTypeContext
emptyRegionTypeContext = (RegionTypeContext Map.empty Map.empty)

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
                 _ -> Nothing



declrsToRegionTypeContext :: (Monad m, MonadRaise m, MonadLogger m) =>
        [AST.Declr]
        -- ^ Declarations
        -> m RegionTypeContext
declrsToRegionTypeContext declrs = do
            -- Determine the parameter types for (region) declarations
            typings <- typeDeclarations declrs
            -- Build the region type context
            accumulate typings 0 emptyRegionTypeContext declrs
    where
        accumulate typings nextRTId ac [] = return ac
        accumulate typings nextRTId ac
            (decl@(AST.RegionDeclr sp rtnam rtparams gddec interps acts):rs) =
                do
                    -- Look up the parameter types.  This should not fail.
                    let !params = map toParam $ Map.findWithDefault
                            (error "declrsToRegionTypeContext: region parameters not determined.")
                            rtnam typings
                    -- Check that there is at least some state intepretation
                    contextualise decl $ when (null interps) $
                        raise MissingStateInterpretation
                    -- Compute the state space (we have just checked the
                    -- precondition for this)
                    let !stateSpace = computeStateSpace interps
                    let transitions = undefined -- TODO
                    let rt = RegionType rtnam params gddec stateSpace transitions interps
                    accumulate typings (nextRTId + 1)
                        (ac {
                            rtcIds = Map.insert rtnam nextRTId (rtcIds ac),
                            rtcRegionTypes = Map.insert nextRTId rt (rtcRegionTypes ac)
                            }) rs
        accumulate typings nextRTId ac (_:rs) =
                        accumulate typings nextRTId ac rs
        toParam (s, vt) = (RTDVar s, vt)

-- |Check that the list of parameters for a region is of the right length and
-- that each parameter is of the appropriate type.
checkRegionParams :: (MonadState s m, AssumptionLenses s,
                MonadReader r m, RTCGetter r,
                MonadRaise m) =>
        RTId -> [(Expr VariableID, AnyExpr)] -> m ()
checkRegionParams rtid params = do
                        rt <- lookupRType rtid
                        let types = map snd $ rtParameters rt
                        if length types == length params then
                                checkParams (2 :: Int) params types
                            else
                                raise $ ArgumentCountMismatch (2 + length types) (2 + length params)
        where
                checkParams n ((e, p) : ps) (t : ts) = do
                        addContext (DescriptiveContext (sourcePos p) $
                                        "In argument " ++ show n) $
                                checkExpressionAtTypeE e t
                        checkParams (n+1) ps ts
                checkParams _ _ _ = return ()

