{-# LANGUAGE FlexibleInstances #-}

import Test.QuickCheck
import Test.QuickCheck.Monadic
import Test.QuickCheck.Arbitrary
import Control.Monad

import Caper.Parser.AST.Annotation

import Infrastructure
import RegionTypes

prop_VBool :: Bool -> Property
prop_VBool b = monadicIO $ do
        r <- run $ isValid $ AssrtPure p0 $ ConstBAssrt p0 b
        assert $ r == b


prop_VEqualityTrue :: Int -> Property
prop_VEqualityTrue n = let m = ConstValExpr p0 (toInteger n) in monadicIO $ do
        r <- run $ isValid $ AssrtPure p0 $ BinaryValAssrt p0 (ValEquality EqualRel) m m
        assert r

prop_VEqualityFalse :: Int -> Int -> Property
prop_VEqualityFalse n m = n /= m ==> monadicIO $ do
        r <- run $ isValid $ AssrtPure p0 $ BinaryValAssrt p0 (ValEquality EqualRel)
                (ConstValExpr p0 (toInteger n)) (ConstValExpr p0 (toInteger m))
        assert $ not r

prop_SBool :: Bool -> Property
prop_SBool b = monadicIO $ do
        r <- run $ isSatisfiable $ AssrtPure p0 $ ConstBAssrt p0 b
        assert $ r == b


prop_SEqualityTrue :: Int -> Property
prop_SEqualityTrue n = let m = ConstValExpr p0 (toInteger n) in monadicIO $ do
        r <- run $ isSatisfiable $ AssrtPure p0 $ BinaryValAssrt p0 (ValEquality EqualRel) m m
        assert r

prop_SEqualityFalse :: Int -> Int -> Property
prop_SEqualityFalse n m = n /= m ==> monadicIO $ do
        r <- run $ isSatisfiable $ AssrtPure p0 $ BinaryValAssrt p0 (ValEquality EqualRel)
                (ConstValExpr p0 (toInteger n)) (ConstValExpr p0 (toInteger m))
        assert $ not r

varVal = VarValExpr p0 . Variable p0
constVal = ConstValExpr p0 . toInteger
assEq x y = AssrtPure p0 $ BinaryValAssrt p0 (ValEquality EqualRel) x y
assNEq x y = AssrtPure p0 $ BinaryValAssrt p0 (ValEquality NotEqualRel) x y

prop_ImpliesEqual :: Int -> Int -> Property
prop_ImpliesEqual n m = n /= m ==> monadicIO $ do
        r <- run $ implies
                (assEq (constVal n) (varVal "x"))
                (AssrtConj p0 (assEq (varVal "x") (constVal n))
                        (assNEq (varVal "x") (constVal m)))
        assert r

data ConstVal = CVC Integer | CVPlus ConstVal ConstVal | CVMinus ConstVal ConstVal | CVTimes ConstVal ConstVal deriving (Show,Eq,Ord)

evalCV :: ConstVal -> Integer
evalCV (CVC x) = x
evalCV (CVPlus x y) = evalCV x + evalCV y
evalCV (CVMinus x y) = evalCV x - evalCV y
evalCV (CVTimes x y) = evalCV x * evalCV y

arbCV :: Int -> Gen ConstVal
arbCV 0 = liftM CVC arbitrary
arbCV n = oneof [liftM CVC arbitrary,
        do
                op <- elements [CVPlus, CVMinus, CVTimes]
                a1 <- arbCV (n `div` 2)
                a2 <- arbCV (n `div` 2)
                return (op a1 a2)
        ]

instance Arbitrary ConstVal where
        arbitrary = sized arbCV

toValExpr :: ConstVal -> ValExpr
toValExpr (CVC x) = ConstValExpr p0 x
toValExpr (CVPlus x y) = BinaryValExpr p0 ValAdd (toValExpr x) (toValExpr y)
toValExpr (CVMinus x y) = BinaryValExpr p0 ValSubtract (toValExpr x) (toValExpr y)
toValExpr (CVTimes x y) = BinaryValExpr p0 ValMultiply (toValExpr x) (toValExpr y)

prop_VExprEqual :: ConstVal -> Property
prop_VExprEqual cv = monadicIO $ do
        r <- run $ isValid $ assEq (toValExpr cv) (ConstValExpr p0 (evalCV cv))
        assert r

data ValCMP = VCMPEq | VCMPNeq | VCMPGt | VCMPGte | VCMPLt | VCMPLte deriving (Eq, Ord, Show)

evalCMP :: ValCMP -> Integer -> Integer -> Bool
evalCMP VCMPEq = (==)
evalCMP VCMPNeq = (/=)
evalCMP VCMPGt = (>)
evalCMP VCMPGte = (>=)
evalCMP VCMPLt = (<)
evalCMP VCMPLte = (<=)

instance Arbitrary ValCMP where
        arbitrary = elements [VCMPEq , VCMPNeq , VCMPGt , VCMPGte , VCMPLt , VCMPLte]

toValBinRel VCMPEq = ValEquality EqualRel
toValBinRel VCMPNeq = ValEquality NotEqualRel
toValBinRel VCMPGt = ValGreater
toValBinRel VCMPGte = ValGreaterOrEqual
toValBinRel VCMPLt = ValLess
toValBinRel VCMPLte = ValLessOrEqual

prop_CMPEq :: ValCMP -> Integer -> Property
prop_CMPEq c n = monadicIO $ do
        r <- run $ isValid $ AssrtPure p0 (BinaryValAssrt p0 (toValBinRel c) (ConstValExpr p0 n) (ConstValExpr p0 n))
        assert $ r == evalCMP c n n

prop_CMPNEq :: ValCMP -> Integer -> Integer -> Property
prop_CMPNEq c n m = n /= m ==> monadicIO $ do
        r <- run $ isValid $ AssrtPure p0 (BinaryValAssrt p0 (toValBinRel c) (ConstValExpr p0 n) (ConstValExpr p0 m))
        assert $ r == evalCMP c n m


data ValPE a = VPENot (ValPE a) | VPECmp ValCMP a a deriving (Eq, Ord, Show)

evalCVPE :: ValPE ConstVal -> Bool
evalCVPE (VPENot x) = not (evalCVPE x)
evalCVPE (VPECmp o a b) = evalCMP o (evalCV a) (evalCV b)

arbCVPE :: Int -> Gen (ValPE ConstVal)
arbCVPE 0 = do
                cmp <- arbitrary
                a1 <- arbCV 0
                a2 <- arbCV 0
                return (VPECmp cmp a1 a2)
arbCVPE n = oneof [
        (do
                cmp <- arbitrary
                a1 <- arbCV (n `div` 2)
                a2 <- arbCV (n `div` 2)
                return (VPECmp cmp a1 a2)),
        liftM VPENot (arbCVPE (n - 1))]

instance Arbitrary (ValPE ConstVal) where
        arbitrary = sized arbCVPE

toPureAssrt :: ValPE ConstVal -> PureAssrt
toPureAssrt (VPENot x) = NotBAssrt p0 (toPureAssrt x)
toPureAssrt (VPECmp o x y) = BinaryValAssrt p0 (toValBinRel o) (toValExpr x) (toValExpr y)

data ValBE a = VBEP (ValPE a) | VBEConj (ValBE a) (ValBE a) deriving (Eq, Ord, Show)

evalCVBE (VBEP x) = evalCVPE x
evalCVBE (VBEConj a b) = evalCVBE a && evalCVBE b

arbCVBE 0 = liftM VBEP (arbCVPE 0)
arbCVBE n = oneof [
        liftM VBEP (arbCVPE n),
        do
                a1 <- arbCVBE (n `div` 2)
                a2 <- arbCVBE (n `div` 2)
                return (VBEConj a1 a2)
        ]

instance Arbitrary (ValBE ConstVal) where
        arbitrary = sized arbCVBE

toAssrt :: ValBE ConstVal -> Assrt
toAssrt (VBEP x) = AssrtPure p0 (toPureAssrt x)
toAssrt (VBEConj a b) = AssrtConj p0 (toAssrt a) (toAssrt b)

prop_VConstValBE :: ValBE ConstVal -> Property
prop_VConstValBE x = monadicIO $ do
        r <- run $ isValid $ toAssrt x
        assert $ r == evalCVBE x

prop_VConstValBETrue :: ValBE ConstVal -> Property
prop_VConstValBETrue x = evalCVBE x ==>
        monadicIO $ do
        r <- run $ isValid $ toAssrt x
        assert r
