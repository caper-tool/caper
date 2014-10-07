
import Test.QuickCheck
import Test.QuickCheck.Arbitrary
import Test.QuickCheck.Property
import Control.Monad
--import Debug.Trace
import Text.Parsec (parse, eof)

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

instance Arbitrary PermExpr where
        arbitrary = sized arb
            where
                arb n | n>=0 =
                        frequency [(1,liftM (VarPermExpr p0) arbitrary),
                                (1,liftM (ConstPermExpr p0) (elements [FullPerm, EmptyPerm])),
                                (n,liftM (UnaryPermExpr p0 Complement) (arb (n-1))),
                                (n,liftM2 (BinaryPermExpr p0 Composition) (arb (n `div` 2)) (arb (n `div` 2)))]


testValExpr :: ValExpr -> Property
testValExpr ve = parseValueExpression (show ve) === ve

testPermExpr :: PermExpr -> Property
testPermExpr pe = case parse permissionExpression "" (show pe) of
        Left e -> counterexample (show e) failed
        Right pe' -> pe' === pe

pseudoPermString :: Gen String
pseudoPermString = sized arb
        where
                arb 0 = return ""
                arb n | n > 0 = do
                        l <- (elements "01p~$xP")
                        r <- (arb (n-1))
                        return (l : r)

stripParensSpaces s = [x | x <- s, x `notElem` "() "]

testPermBack :: Gen Property
testPermBack = liftM tpb pseudoPermString
        where
                tpb s = case parse (do {r <- permissionExpression; eof; return r}) "" s of
                        Left _ -> property succeeded
                        Right pe' -> verbose $ stripParensSpaces (show pe') === s
