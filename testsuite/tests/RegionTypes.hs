module RegionTypes where
import Control.Lens
import qualified Data.Map as Map
import Control.Monad.RWS
import Data.Functor.Identity

import qualified Caper.Utils.AliasingMap as AM
import Caper.ProverDatatypes
import Caper.Prover
import Caper.Provers
import Caper.Guards
import Caper.RegionTypes
import Caper.Regions
import Caper.SymbolicState

-- A[_] * ((B * C) + D[_])
t_TLGuardType0 :: TopLevelGuardTypeAST
t_TLGuardType0 = SomeGT $ ProductGT (NamedPermissionGT "A")
                (SumGT (ProductGT (NamedGT "B") (NamedGT "C"))
                        (NamedPermissionGT "D"))


instance RTCGetter a => RTCGetter (b, a) where
        theRTContext = to $ (^.theRTContext) . snd
instance Provers a => Provers (a, b) where
        permissionsProver = permissionsProver . fst
        valueProver = valueProver . fst

t_TransitionRules0 = [
        TransitionRule (GD $ Map.fromList [("A", PermissionGP PEFull)]) () (VEConst 1) (VEConst 2),
        TransitionRule (GD $ Map.fromList [("C", NoGP)]) () (VEConst 2) (VEConst 3),
        TransitionRule (GD $ Map.fromList [("A", PermissionGP $ PEVar $ RTDVar "p")]) () (VEConst 3) (VEConst 4),
        TransitionRule (GD $ Map.fromList [("B", NoGP), ("C", NoGP)]) () (VEConst 4) (VEConst 1)
        ]

t_RegionType0 :: RegionType
t_RegionType0 = RegionType "Test" [] t_TLGuardType0 (StateSpace (Just 1) (Just 4))
                t_TransitionRules0
                ()

t_RTContext0 :: RegionTypeContext
t_RTContext0 = RegionTypeContext (Map.fromList [("Test",0)]) (Map.fromList [(0,t_RegionType0)])

emptyRTContext :: RegionTypeContext
emptyRTContext = RegionTypeContext Map.empty Map.empty
