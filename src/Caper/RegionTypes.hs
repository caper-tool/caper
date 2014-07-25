{-# LANGUAGE RankNTypes #-}
module Caper.RegionTypes where
import Control.Monad
import Control.Monad.Reader.Class
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Monoid
import Data.Foldable
import Control.Lens
import Data.Maybe
import Data.List (intercalate)

import Caper.Guards
import Caper.ProverDatatypes



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
                rtGuardType :: TopLevelGuardTypeAST,
                rtStateSpace :: StateSpace,
                rtTransitionSystem :: [TransitionRule],
                rtInterpretation :: () -- TODO: replace with appropriate repr. of assertion
        }

instance Show RegionType where
        show (RegionType nm params gt ss ts interp) =
                "region " ++ nm ++ "(" ++ intercalate "," (map (show . fst) params) ++ ") {\n" ++
                "  guards : " ++ show gt ++ "\n" ++
                "  transitions {\n    " ++ intercalate "\n    " (map show ts) ++ "\n  }\n" ++
                "}"


rtWeakGT = topLevelToWeakGuardType . rtGuardType

rtParamVars :: RegionType -> Set RTDVar
rtParamVars = Set.fromList . map fst . rtParameters

-- StateSpace

-- ssLowerBound and ssUpperBound are the (inclusive) lower
-- and upper bounds of the state space.
-- invariant: ssLowerBound <= ssUpperBound (if both are not Nothing)
data StateSpace = StateSpace {
                ssLowerBound :: Maybe Int,
                ssUpperBound :: Maybe Int
                }
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
trVariables (TransitionRule g prd pre post) = Set.fromList $ toList g ++ toList pre ++ toList post

instance Show TransitionRule where
        show (TransitionRule gd pred pre post) =
                show gd ++ " : " ++ show pre ++ " ~> " ++ show post

data RegionTypeContext = RegionTypeContext
        {
                rtcIds :: Map String RTId,
                rtcRegionTypes :: Map RTId RegionType
        }

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

instance RTCGetter RegionTypeContext where
        theRTContext = to id

createRegionTypeContext :: [RegionType] -> RegionTypeContext
createRegionTypeContext = crtcs 0 (RegionTypeContext Map.empty Map.empty)
        where
                crtcs nextRTId ac [] = ac
                crtcs nextRTId ac (r : rs) = crtcs (nextRTId + 1)
                        (ac { rtcIds = Map.insert (rtRegionTypeName r) nextRTId (rtcIds ac), rtcRegionTypes = Map.insert nextRTId r (rtcRegionTypes ac) })
                        rs
