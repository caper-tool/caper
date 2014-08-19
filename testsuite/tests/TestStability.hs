import Test.HUnit
import Control.Monad

import Caper.StabilityCheck
import Caper.Parser.AST.Annotation

import RegionTypes
import Infrastructure

test0 = runWithRTC' t_RTContext0 $ checkStability
        (AssrtSpatial p0 $ SACell (Cell p0 (VarValExpr p0 (Variable p0 "x")) (ConstValExpr p0 0)))

stab :: Assrt -> IO Bool
stab = runWithRTC' t_RTContext0 . checkStability

nstab = liftM not . stab

cve = ConstValExpr p0
vr = VarValExpr p0 . Variable p0
x === y = AssrtPure p0 (BinaryValAssrt p0 (ValEquality EqualRel) x y)
x /== y = AssrtPure p0 (BinaryValAssrt p0 (ValEquality NotEqualRel) x y)
aregs = (AssrtSpatial p0 (SARegion $ Region p0 "Test" "r" [] (VarValExpr p0 (Variable p0 "s"))))

(&*&) = AssrtConj p0

a0 = (AssrtSpatial p0 $ SACell (Cell p0 (VarValExpr p0 (Variable p0 "x")) (ConstValExpr p0 0)))
a1 = aregs
a2 = aregs &*& (vr "x" === cve 1)
a3 = aregs &*& (vr "s" === cve 1)
a4 = aregs &*& (vr "s" /== cve 2) &*& (vr "s" /== cve 4)
a5 = a4 &*& (AssrtSpatial p0 (SAGuards $ Guards p0 "r" [PermGuard p0 "A" (ConstPermExpr p0 FullPerm)]))


tests = test [ "Stable" ~: test [ stab t ~? "Should be stable: " ++ show t | t <-
                        [a0, a1, a2] ],
        "Unstable" ~: test [ nstab t ~? "Should not be stable: " ++ show t | t <-
                        [a3, a4] ]]
