{-# LANGUAGE BangPatterns #-}
module Caper.Utils.FloydWarshall where
import Data.Vector (Vector)
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as VM
import Data.Foldable (forM_, foldl', foldMap)


class Floydable a where
        -- Compute the minimum of two 'distances'
        fmin :: a -> a -> a
        -- Combine two 'distances'
        fadd :: a -> a -> a
        -- Infinite 'distance'
        finfty :: a
        -- It should be that the following equalities hold
        -- (upto some suitable notion of equality):
        -- fmin x y = fmin y x
        -- fadd x y = fadd y x
        -- fadd finfty x = finfty
        -- fmin finfty x = x

type Matrix a = Vector (Vector a)

matrixGet :: Matrix a -> Int -> Int -> a
matrixGet mx x y = (mx V.! x) V.! y

floydInit :: Int -> (Int -> Int -> a) -> Matrix a
--floydInit d f = V.generate d (\x -> V.generate d (\y -> f x y))
floydInit d f = V.create $ do
        mx <- VM.new d
        forM_ [0..(d-1)] $ \i ->
                VM.write mx i $ V.create $ do
                        row <- VM.new d
                        forM_ [0..(d-1)] $ \j -> do
                                let !entry = f i j
                                VM.write row j entry
                        return row
        return mx

floydInitM :: Monad m => Int -> (Int -> Int -> m a) -> m (Matrix a)
floydInitM d f = V.generateM d (V.generateM d . f)

floydStep :: (Floydable a) => Int -> Matrix a -> Matrix a
floydStep k !mx = floydInit (V.length mx) (\i j -> fmin (matrixGet mx i j) (fadd (matrixGet mx i k) (matrixGet mx k j)))

runFloyd :: (Floydable a) => Matrix a -> Matrix a
runFloyd mx = foldl' (flip floydStep) mx [0..(V.length mx - 1)]

instance Floydable Bool where
        fmin = (||)
        fadd = (&&)
        finfty = False
{-
test1 = floydInit 10 (==)
test2 = floydInit 10 (\a b -> a + 1 == b)
test3 = floydInit 100 (\a b -> a + 4 == b || a == b + 4)

showbm :: Matrix Bool -> String
showbm = foldMap ((++"\n") . foldMap (\b -> if b then "1" else "."))
printbm = putStrLn . showbm
-}