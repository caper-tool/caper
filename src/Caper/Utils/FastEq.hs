{-# LANGUAGE MagicHash #-}
module Caper.Utils.FastEq where

import GHC.Exts

-- | A (potentially) faster equality that uses pointer equality as a shortcut.
-- There are a few caveats and subtle differences from normal equality.
--
-- >>> let x = [1..] in x ==== x
-- True
-- >>> let x = [1..] in x == x
-- /diverges/
-- >>> let x = 1 : undefined in x ==== x
-- True
-- >>> let x = 1 : undefined in x == x
-- *** Exception: Prelude.undefined
--
-- The above occur since the values being compared are only head-normalised.
-- If @====@ is only used with values that are finite and cannot throw
-- exceptions when normalised, then it should behave like equality.

(====) :: Eq a => a -> a -> Bool
a ==== b = a `seq` b `seq` case reallyUnsafePtrEquality# a b of
        1# -> True
        _ -> a == b