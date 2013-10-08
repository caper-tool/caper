import Test.HUnit
import ProverDatatypes
import qualified Data.Map as Map

vx = VIDNamed () "x"
vx0 = head $ freshen vx
vy = VIDNamed () "y"
vix = VIDInternal () "X"
viy = VIDInternal () "Y"
viy0 = head $ freshen viy

f1 = FOFForAll vx $ FOFExists viy $ FOFAnd (FOFAtom $ VAEq (return vx) (return vy)) (FOFNot $ FOFAtom $ VAEq (return vx) (return viy))

f1s = FOFForAll vx0 $ FOFExists viy $ FOFAnd (FOFAtom $ VAEq (return vx0) (return vx)) (FOFNot $ FOFAtom $ VAEq (return vx0) (return viy))

sub1 v = Map.findWithDefault (return v) v (Map.fromList [(vx, VEConst 27), (viy, return vix), (vy, return vx)])


testCASub1 = "exprCASub sub1 f1 == f1s" ~: exprCASub sub1 f1 ~?= f1s

testCASub2 = "exprCASub" ~: exprCASub sub1 (FOFAtom (return vx)) ~?= FOFAtom (VEConst 27)
testCASub3 = "exprCASub" ~: exprCASub sub1 (FOFForAll vy $ FOFAtom (VAEq (return vx) (VEConst 20))) ~?= (FOFForAll vy $ FOFAtom (VAEq (VEConst 27) (VEConst 20)))
testCASub4 = "exprCASub" ~: exprCASub sub1 (FOFForAll vx $ FOFAtom (VAEq (return vx) (VEConst 20))) ~?= (FOFForAll vx $ FOFAtom (VAEq (return vx) (VEConst 20)))

--testCASub5 = "exprCASub" ~: exprCASub 

tests = TestList [testCASub1, testCASub2, testCASub3, testCASub4]

main = runTestTT tests
