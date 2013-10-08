import Test.HUnit
import Prover
import ProverDatatypes

vx = VIDNamed () "x"
vy = VIDNamed () "y"
vz = VIDNamed () "z"


pe0 = PEZero
pe1 = PECompl PEZero
pe2 = PESum (PEVar vx) pe1

ve0 = VEConst 27
ve1 = VEVar vz
ve2 = VEPlus ve0 ve1
ve3 = VEVar vy

sub v = if v == vy then PermissionExpr pe0 else return v

-- Should error
testFoo = exprCASub sub (exprEquality (toExpr ve2) (toExpr ve3))


