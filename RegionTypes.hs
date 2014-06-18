module RegionTypes where
import Control.Monad
import Data.Map (Map)
import qualified Data.Map as Map
import Guards
import ProverDatatypes



-- The internal representation of a region type identifier
type RTId = Integer

data RegionType = RegionType
        {
                rtRegionTypeName :: String,
                rtGuardType :: GuardTypeAST,
                rtStateSpace :: StateSpace,
                rtTransitionSystem :: [TransitionRule],
                rtInterpretation :: () -- TODO: replace with appropriate repr. of assertion
        }

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

newtype TrVar = TrVar String deriving (Eq,Ord)
instance Show TrVar where
        show (TrVar s) = s
instance StringVariable TrVar where
        varToString (TrVar s) = s


data TransitionRule = TransitionRule
        {
                -- The guard that is required to perform the transition
                trGuard :: GuardAST TrVar,
                -- Some (pure) predicate that conditions the transition
                -- (Not Implemented Yet)
                trPredicate :: (),
                -- An expression describing the state to transition from
                trPreState :: ValueExpression TrVar,
                -- An expression describing the state to transition to
                trPostState :: ValueExpression TrVar
        }

instance Show TransitionRule where
        show (TransitionRule gd pred pre post) =
                show gd ++ " : " ++ show pred ++ " ~> " ++ show post

data RegionTypeContext = RegionTypeContext
        {
                rtcIds :: Map String RTId,
                rtcRegionTypes :: Map RTId RegionType
        }

createRegionTypeContext :: [RegionType] -> RegionTypeContext
createRegionTypeContext = crtcs 0 (RegionTypeContext Map.empty Map.empty)
        where
                crtcs nextRTId ac [] = ac
                crtcs nextRTId ac (r : rs) = crtcs (nextRTId + 1)
                        (ac { rtcIds = Map.insert (rtRegionTypeName r) nextRTId (rtcIds ac), rtcRegionTypes = Map.insert nextRTId r (rtcRegionTypes ac) })
                        rs
