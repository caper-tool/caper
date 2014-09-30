module RegionTypes where
import Control.Lens
import qualified Data.Map as Map
import Control.Monad.RWS
import Data.Functor.Identity
import Text.Parsec.Pos

import qualified Caper.Utils.AliasingMap as AM
import Caper.ProverDatatypes
import Caper.Prover
import Caper.Provers
import Caper.Guards
import Caper.RegionTypes
import Caper.Regions
import Caper.SymbolicState
import Caper.Parser.AST.Annotation

p1 = initialPos "[None]"

-- A[_] * ((B * C) + D[_])
t_TLGuardType0 :: TopLevelGuardDeclr
t_TLGuardType0 = SomeGuardDeclr $ ProductGD p1 (PermissionGD p1 "A")
                (SumGD p1 (ProductGD p1 (NamedGD p1 "B") (NamedGD p1 "C"))
                        (PermissionGD p1 "D"))


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
