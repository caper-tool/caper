
import Test.QuickCheck
import Test.QuickCheck.Arbitrary
import Control.Monad
--import Debug.Trace

import Caper.Parser.AST
import Caper.Parser.Parser

import Infrastructure

arbid = oneof [return [l] | l <- ['a'..'z']]

instance Arbitrary VarExpr where
        arbitrary = oneof [liftM (Variable p0) arbid,
                return (WildCard p0)]

instance Arbitrary ValBinOp where
        arbitrary = oneof $ map return [ValAdd, ValSubtract, ValMultiply, ValDivide]

arbnat = sized $ \n -> choose (0 :: Integer, toInteger n)

instance Arbitrary ValExpr where
        arbitrary = sized arb
            where
                arb n | n>=0 =
                        frequency [(1,liftM (VarValExpr p0) arbitrary),
                                (1,liftM (ConstValExpr p0) arbnat),
                                (n,liftM (UnaryValExpr p0 ValNegation) (arb (n-1))),
                                (n,liftM3 (BinaryValExpr p0) arbitrary (arb (n `div` 2)) (arb (n `div` 2))),
                                (n,(do
                                        l <- choose (1,n)
                                        s <- vectorOf l (arb (n `div` l))
                                        return $ SetValExpr p0 s))
                                ]

testValExpr :: ValExpr -> Bool
testValExpr ve = parseValueExpression (show ve) == ve
