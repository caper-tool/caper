{-# LANGUAGE FlexibleContexts, CPP #-}
module Caper.FirstOrder.Tests (tests) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.QuickCheck (testProperty)
import Test.Tasty.HUnit (testCase)
import Test.HUnit (Assertion, (@?=))
import Test.QuickCheck as QC
import Test.QuickCheck.Monadic as QC

import qualified Data.Set as Set

import Caper.ProverDatatypes
--import PermissionsInterface
import Caper.Provers.Permissions.Internal
import Caper.Provers.Permissions.E
--import Caper.Provers.Permissions.SMT
import Caper.FirstOrder 


tests :: TestTree
tests = testGroup "Caper.FirstOrder" [
  testProperty "close x == simplify (close x)"
    prop_SimplEquiv
  ]

class Sized c where
  size :: c -> Int

instance Sized (PermissionExpression v) where
  size (PESum x y) = 1 + size x + size y
  size (PECompl x) = 1 + size x
  size _ = 1

instance Sized (PermissionAtomic v) where
  size (PAEq e1 e2) = 1 + size e1 + size e2
  size (PADis e1 e2) = 1 + size e1 + size e2

instance Sized (a v) => Sized (FOF a v) where
  size (FOFForAll _ f) = 1 + size f
  size (FOFExists _ f) = 1 + size f
  size (FOFAtom a) = size a
  size (FOFAnd x y) = size x + size y
  size (FOFOr x y) = size x + size y
  size (FOFImpl x y) = size x + size y
  size (FOFNot x) = size x
  size _ = 0

newtype StringVar = StringVar String
                  deriving (Eq, Ord)

instance Show StringVar where
  show (StringVar s) = s

instance Arbitrary StringVar where
  arbitrary = sized $ \n -> do
    x <- choose (0, toInteger $ floor $ sqrt $ fromInteger $ toInteger n)
    return . StringVar $ "x" ++ show x

instance Arbitrary v => Arbitrary (PermissionExpression v) where
  arbitrary = sized $ \n -> arb' n n
    where
      arb' 0 l = frequency [(4, return PEFull),
                            (4, return PEZero),
                            (l, PEVar <$> arbitrary)]
      arb' n l = frequency [(2, return PEFull),
                            (2, return PEZero),
                            (l, PEVar <$> arbitrary),
                            (l, arbsum (n `div` 2) l),
                            (l `div` 2, arbcompl (n `div` 2) l) ]
      arbsum n l = PESum <$> arb' n l <*> arb' n l
      arbcompl n l = PECompl <$> arb' n l

instance Arbitrary v => Arbitrary (PermissionAtomic v) where
  arbitrary = do
    e1 <- arbitrary
    e2 <- arbitrary
    oneof . map return $ [PAEq e1 e2, PADis e1 e2]

instance (Arbitrary v, Arbitrary (a v), Eq v, Foldable a) => Arbitrary (FOF a v) where
  arbitrary = sized (\n -> if n > 100 then arb 100 else arb n)
    where
      arb 0 = frequency [(1,return FOFTrue),
                         (1,return FOFFalse),
                         (8, FOFAtom <$> arbitrary)]
      arb n = frequency [(1,return FOFTrue),
                         (1,return FOFFalse),
                         (8, FOFAtom <$> arbitrary),
                         (8, FOFNot <$> (arb $ n `div` 2)),
                         (24,do
                             l <- arb $ n `div` 2
                             r <- arb $ n `div` 2
                             oneof . map return $ [FOFAnd l r, FOFOr l r, FOFImpl l r]),
                         (12,do
                             (v, f') <- suchThat (bvc n) (\(vv, ff) -> not $ boundIn vv ff)
                             oneof . map return $ [FOFExists v f', FOFForAll v f'])]
      bvc n = do
        v <- arbitrary
        f' <- arb $ floor (sqrt $ fromIntegral n) - 1
        return (v, f')

close :: (Eq v, Ord v, Foldable a) => FOF a v -> FOF a v
close f = foldr (\x -> if freeIn x f then FOFForAll x else id) f (foldr (Set.insert) Set.empty f)

prop_SimplEquiv :: FOF PermissionAtomic StringVar -> Property
prop_SimplEquiv x = quantifierDepth (close x) == 4 ==> monadicIO $ do
  r2 <- run $ permCheckTree (fmap show (simplify (close x)))
  r1 <- run $ permCheckTree (fmap show (close x))
  assert $ r1 == r2

-- prop_ProverEquiv :: FOF PermissionAtomic StringVar -> Property
-- prop_ProverEquiv x = quantifierDepth x <= 6 ==> let x' = simplify (close x) in
--                         quantifierDepth x' <= 4 ==> monadicIO $ do
--                                 r1 <- run $ time $ permCheckTree (fmap show x')
--                                 r2 <- run $ do
--                                         epp <- makeEPProver "C:\\Users\\tyoung\\Local Documents\\eprover\\E\\PROVER\\eprover.exe" 10000
--                                         time $ epp (fmap show x')
--                                 assert $ r1 == r2

-- timeoutSolver :: Int -> PermissionsProver -> PermissionsProver
-- timeoutSolver n f x = timeout n (f x) >>= return . join


-- prop_ProverEquivSMT :: FOF PermissionAtomic StringVar -> Property
-- prop_ProverEquivSMT x = quantifierDepth x <= 6 ==> let x' = simplify (close x) in
--                         quantifierDepth x' <= 5 ==> monadicIO $ do
--                                 run $ putStrLn "Z3 "
--                                 r2 <- run $ time $ permCheckZ3 (Just 10000) x'
--                                 run $ putStrLn "BigInt "
--                                 r1 <- run $ time $ (timeoutSolver (10^7) permCheckBigInt) (fmap show x')
--                                 assert $ r1 == r2
