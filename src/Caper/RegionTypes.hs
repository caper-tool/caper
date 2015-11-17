{-# LANGUAGE RankNTypes, BangPatterns, MultiParamTypeClasses #-}
module Caper.RegionTypes where

import Prelude hiding (notElem, mapM_)
import Control.Monad hiding (mapM_)
import Control.Monad.Reader.Class
import Control.Monad.State hiding (mapM_)
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
import Caper.FreeVariables
import Caper.Guards
import Caper.ProverDatatypes
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


data RegionType = RegionType
        {
                rtSourcePos :: SourcePos,
                rtRegionTypeName :: String,
                rtParameters :: [(RTDVar, VariableType)],
                rtGuardType :: AST.TopLevelGuardDeclr,
                rtStateSpace :: StateSpace,
                rtTransitionSystem :: [TransitionRule],
                rtInterpretation :: [AST.StateInterpretation]
        }

instance Contextual RegionType where
        toContext rt = DescriptiveContext (rtSourcePos rt) $
                "In a region type declaration named '" ++ rtRegionTypeName rt ++ "'"

instance Show RegionType where
        show (RegionType _ nm params gt ss ts interp) =
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

actionToTransitionRule :: (MonadRaise m, Monad m) => [RTDVar] -> AST.Action -> m TransitionRule
actionToTransitionRule params act@(AST.Action _ conds gds prest postst) =
        contextualise act $ do
            unless (null conds) $ raise $ SyntaxNotImplemented "predicated transitions"
            (gg, prec, post) <- flip evalStateT freshVars $ do
                gg <- generateGuard varExprToRTDVar gds
                prec <- generateValueExpr varExprToRTDVar prest
                post <- generateValueExpr varExprToRTDVar postst
                return (gg,prec,post) 
            return $ TransitionRule gg () prec post
    where
        theVars = params ++ (map RTDVar . mapMaybe AST.unVarExpr . Set.toList . freeVariables) act
        freshVars = filter (`notElem` theVars) [RTDVar ("WILDCARD" ++ show x) | x <- [(0::Int)..]]
        nextFresh = state (head &&& tail)
        varExprToRTDVar (AST.Variable _ s) = return (RTDVar s)
        varExprToRTDVar (AST.WildCard _) = nextFresh

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
                 _ -> Nothing

checkActionsGuards :: (Monad m, MonadRaise m) =>
        AST.TopLevelGuardDeclr -> [AST.Action] -> m ()
checkActionsGuards tlgd@(AST.SomeGuardDeclr gd) = mapM_ $ \a -> let grd = AST.actionGuard a in
        contextualise a $ do            
            g <- generateGuard (const (return ())) grd
            unless (checkGuardAtType g (toWeakGuardType gd)) $
                raise $ GuardInconsistentWithGuardType (show grd) (show tlgd)
checkActionsGuards tlgd@AST.ZeroGuardDeclr = mapM_ $ \a -> let grd = AST.actionGuard a in
        contextualise a $            
            unless (null grd) $ raise $ GuardInconsistentWithGuardType (show grd) (show tlgd)

declrsToRegionTypeContext :: (Monad m, MonadRaise m, MonadLogger m) =>
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
                    -- Check that the action guards conform to the guard algebra
                    checkActionsGuards gddec acts
                    -- Check that there is at least some state interpretation
                    contextualise decl $ when (null interps) $
                        raise MissingStateInterpretation
                    -- Compute the state space (we have just checked the
                    -- precondition for this)
                    let !stateSpace = computeStateSpace interps
                    transitions <- mapM (actionToTransitionRule (map fst params)) acts
                    let rt = RegionType sp rtnam params gddec stateSpace transitions interps
                    accumulate typings (nextRTId + 1)
                        (ac {
                            rtcIds = Map.insert rtnam nextRTId (rtcIds ac),
                            rtcRegionTypes = Map.insert nextRTId rt (rtcRegionTypes ac)
                            }) rs
        toParam (s, vt) = (RTDVar s, vt)

