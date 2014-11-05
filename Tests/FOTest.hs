{-# LANGUAGE FlexibleContexts #-}

import Test.QuickCheck
import Control.Monad hiding (forM_)
import Prelude hiding (foldl, foldr, concat)
import Data.Foldable
import qualified Data.Set as Set
import Test.QuickCheck.Monadic
import Text.Printf
--import Control.Exception
import System.CPUTime
import Data.Time.Clock
import Control.Monad.IO.Class
import System.Timeout
import System.Win32.Time
import Data.List (intercalate)

import System.IO.Unsafe


import Caper.ProverDatatypes
--import PermissionsInterface
import Caper.PermissionsI
import Caper.PermissionsE
import Caper.PermissionsSMT
import Caper.FirstOrder



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

newtype StringVar = StringVar String deriving (Eq, Ord)
instance Show StringVar where
        show (StringVar s) = s

instance Arbitrary StringVar where
        arbitrary = sized (\n -> do
                x <- choose (0, toInteger $ floor $ sqrt $ fromInteger $ toInteger n)
                return $ StringVar $ "x" ++ show x)

instance Arbitrary v => Arbitrary (PermissionExpression v) where
        arbitrary = sized (\n -> arb' n n)
                where
                        arb' 0 l = frequency [(4,return PEFull),(4,return PEZero),(l,liftM PEVar arbitrary)]
                        arb' n l = frequency [(2,return PEFull),(2,return PEZero),(l,liftM PEVar arbitrary), (l,arbsum (n `div` 2) l), (l `div` 2,arbcompl (n `div` 2) l) ]
                        arbsum n l = do
                                s1 <- arb' n l
                                s2 <- arb' n l
                                return $ PESum s1 s2
                        arbcompl n l = do
                                s <- arb' n l
                                return $ PECompl s

instance Arbitrary v => Arbitrary (PermissionAtomic v) where
        arbitrary = do
                e1 <- arbitrary
                e2 <- arbitrary
                oneof [return $ PAEq e1 e2, return $ PADis e1 e2]

instance (Arbitrary v, Arbitrary (a v), Eq v, Foldable a) => Arbitrary (FOF a v) where
        arbitrary = sized (\n -> if n > 100 then arb 100 else arb n)
                where
                        arb 0 = frequency [(1,return FOFTrue),(1,return FOFFalse),(8,liftM FOFAtom arbitrary)]
                        arb n = frequency [(1,return FOFTrue),(1,return FOFFalse),(8,liftM FOFAtom arbitrary),
                                (8,liftM FOFNot (arb $ n `div` 2)),
                                (24,do
                                        l <- arb $ n `div` 2
                                        r <- arb $ n `div` 2
                                        oneof [return $ FOFAnd l r, return $ FOFOr l r, return $ FOFImpl l r]),
                                (12,do
                                        (v, f') <- suchThat (bvc n) (\(vv, ff) -> not $ boundIn vv ff)
                                        oneof [return $ FOFExists v f', return $ FOFForAll v f'])]
                        bvc n = do
                                        v <- arbitrary
                                        f' <- arb $ floor (sqrt $ fromIntegral n) - 1
                                        return (v, f')

close :: (Eq v, Ord v, Foldable a) => FOF a v -> FOF a v
close f = foldr (\x -> if freeIn x f then FOFForAll x else id) f (foldr (Set.insert) Set.empty f)

prop_SimplEquiv :: FOF PermissionAtomic StringVar -> Property
prop_SimplEquiv x = quantifierDepth (close x) == 4 ==> monadicIO $ do
--                        run $ putStrLn $ "######" ++  (show $ quantifierDepth x)
                        let x' = close x
                        run $ do
                                putStrLn (show x')
                                putStrLn (show (simplify x'))
                                putStrLn "================"
                        r2 <- run $ time $ permCheckTree (fmap show (simplify x'))
                        r1 <- run $ time $ permCheckTree (fmap show x')
                        assert $ r1 == r2

prop_ProverEquiv :: FOF PermissionAtomic StringVar -> Property
prop_ProverEquiv x = quantifierDepth x <= 6 ==> let x' = simplify (close x) in
                        quantifierDepth x' <= 4 ==> monadicIO $ do
                                r1 <- run $ time $ permCheckTree (fmap show x')
                                r2 <- run $ do
                                        epp <- makeEPProver "C:\\Users\\tyoung\\Local Documents\\eprover\\E\\PROVER\\eprover.exe" 10000
                                        time $ epp (fmap show x')
                                assert $ r1 == r2

timeoutSolver :: Int -> PermissionsProver -> PermissionsProver
timeoutSolver n f x = timeout n (f x) >>= return . join


prop_ProverEquivSMT :: FOF PermissionAtomic StringVar -> Property
prop_ProverEquivSMT x = quantifierDepth x <= 6 ==> let x' = simplify (close x) in
                        quantifierDepth x' <= 5 ==> monadicIO $ do
                                liftIO $ putStrLn "Z3 "
                                r2 <- run $ time $ permCheckZ3 (Just 10000) x'
                                liftIO $ putStrLn "BigInt "
                                r1 <- run $ time $ (timeoutSolver (10^7) permCheckBigInt) (fmap show x')
                                assert $ r1 == r2
                                        

--main = quickCheck prop_ProverEquivSMT

args' = stdArgs {maxSize = 6}

pcf :: Integer
{-# NOINLINE pcf #-}
pcf = unsafePerformIO queryPerformanceFrequency

time :: Show t => IO t -> IO t
time a = do
    start <- queryPerformanceCounter
    v <- a
    seq v $ print v
    end <- queryPerformanceCounter
    let t = (fromInteger (end - start)) / (fromInteger pcf)
    printf "Computation time: %0.6f sec\n" (t :: Double)
    --let diff = (fromIntegral (end - start)) / (10^12)
    --printf "Computation time: %0.6f sec\n" (diff :: Double)
    return v

doTime :: IO t -> IO (t, Float)
doTime a = do
        start <- queryPerformanceCounter
        v <- a
        end <- v `seq` queryPerformanceCounter
        let t = (fromInteger (end - start)) / (fromInteger pcf)
        return (v, t)


{-
time :: Show t => IO t -> IO t
time a = do
    start <- getCurrentTime -- getCPUTime
    v <- a
    seq v $ print v
    end <- getCurrentTime -- seq v getCPUTime
    putStrLn $ "Computation time: " ++ show (diffUTCTime end start)
    --let diff = (fromIntegral (end - start)) / (10^12)
    --printf "Computation time: %0.6f sec\n" (diff :: Double)
    return v

doTime :: IO t -> IO (t, Float)
doTime a = do
        start <- getCurrentTime
        v <- a
        end <- v `seq` getCurrentTime
        return (v, fromRational $ toRational (diffUTCTime end start))
-}        

fpf6 = FOFForAll "a" $ FOFForAll "b" $ FOFForAll "c" $ FOFForAll "d" $
        FOFImpl (FOFAtom $ PAEq (PESum (PEVar "a") (PEVar "b")) (PESum (PEVar "c") (PEVar "d"))) $
            FOFExists "ac" $ FOFExists "ad" $ FOFExists "bc" $ FOFExists "bd" $
            FOFAnd
                (FOFAnd (FOFAtom $ PAEq (PEVar "a") (PESum (PEVar "ac") (PEVar "ad")))
                        (FOFAtom $ PAEq (PEVar "b") (PESum (PEVar "bc") (PEVar "bd"))))
                (FOFAnd (FOFAtom $ PAEq (PEVar "c") (PESum (PEVar "ac") (PEVar "bc")))
                        (FOFAtom $ PAEq (PEVar "d") (PESum (PEVar "ad") (PEVar "bd"))))

samples :: IO [FOF PermissionAtomic StringVar]
samples = generate (sequence (concat [replicate 10 (liftM (simplify . close) $ resize n arbitrary) | n <- [1..100]]))

myProvers :: IO [PermissionsProver]
myProvers = do
        let timeout = 1000
        epp <- makeEPProver "C:\\Users\\tyoung\\Local Documents\\eprover\\E\\PROVER\\eprover.exe" timeout
        return [epp,
                permCheckZ3 (Just timeout),
                (timeoutSolver (timeout * 1000) permCheckBigInt),
                (timeoutSolver (timeout * 1000) permCheckTree)]


testSample :: [PermissionsProver] -> FOF PermissionAtomic StringVar -> IO String
testSample provers f = do
                let f' = fmap show f
                rs <- sequence [doTime (p f') | p <- provers]
                return $ intercalate "," $ show f' : show (size f') : show (quantifierDepth f') :
                                [show t ++ "," ++ showres r | (r, t) <- rs]
        where
                showres Nothing = "Timeout"
                showres (Just x) = show x


main = do
        ss <- samples
        ps <- myProvers
        forM_ ss $ \s -> do
                r <- testSample ps s
                appendFile "permTests.csv" $ r ++ "\n"

