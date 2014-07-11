import Control.Lens
import qualified Data.Map as Map
import Control.Monad.RWS
import Data.Functor.Identity

import qualified Utils.AliasingMap as AM
import ProverDatatypes
import Prover
import Provers
import Guards
import RegionTypes
import Regions
import SymbolicState


-- A[_] * ((B * C) + D[_])
myTLGT :: TopLevelGuardTypeAST
myTLGT = SomeGT $ ProductGT (NamedPermissionGT "A")
                (SumGT (ProductGT (NamedGT "B") (NamedGT "C"))
                        (NamedPermissionGT "D"))

myTLWGT = topLevelToWeakGuardType myTLGT

instance RTCGetter a => RTCGetter (b, a) where
        theRTContext = to $ (^.theRTContext) . snd
instance Provers a => Provers (a, b) where
        permissionsProver = permissionsProver . fst
        valueProver = valueProver . fst

myTRs = [
        TransitionRule (GD $ Map.fromList [("A", PermissionGP PEFull)]) () (VEConst 1) (VEConst 2),
        TransitionRule (GD $ Map.fromList [("C", NoGP)]) () (VEConst 2) (VEConst 3),
        TransitionRule (GD $ Map.fromList [("A", PermissionGP $ PEVar $ RTDVar "p")]) () (VEConst 3) (VEConst 4),
        TransitionRule (GD $ Map.fromList [("B", NoGP), ("C", NoGP)]) () (VEConst 4) (VEConst 1)
        ]

myRT :: RegionType
myRT = RegionType "Test" [] myTLGT (StateSpace (Just 1) (Just 4))
                myTRs
                ()

myRTC :: RegionTypeContext
myRTC = RegionTypeContext (Map.fromList [("Test",0)]) (Map.fromList [(0,myRT)])

runFromRTC :: (MonadIO m) => RegionTypeContext -> SymbState Assumptions ->
                MSState (ProverRecord, RegionTypeContext) m a -> m a
runFromRTC rtc ss mop = do
                ps <- liftIO initProvers
                (a, s, w) <- runRWST mop (ps, rtc) ss
                return a

runFromRTCemp rtc = runFromRTC rtc emptySymbState

setupRegion :: (MonadIO m, MonadState s m, RegionLenses s, AssumptionLenses s,
                MonadReader r m, RTCGetter r, Provers r) =>
                m ()
setupRegion = do
                p <- newAvar "p"
                bindVarsAs (Identity p) VTPermission
                assumeFalse $ var p `PAEq` PEZero
                r <- newAvar "r"
                bindVarsAs (Identity r) VTRegionID
                (Just testID) <- view $ lookupRTName "Test"  
                regions %= AM.insert r (Region True (Just (RegionInstance testID [])) (Just $ VEConst 1) (GD $ Map.fromList [("A", PermissionGP (var p))]))
