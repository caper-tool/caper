-- |This module provides a function for finding near matches to a
-- string from a given list.
--
-- This currently uses a very simple algorithm.  It might be nice to use
-- something cleverer, e.g. based on Levenshtein distance, but then again
-- it might not.
module Caper.Utils.SimilarStrings where


-- |Filters the strings to those which are within one edit of
-- the provided string.  An edit here is an insertion, deletion,
-- substitution or transposition.
similarStrings :: String -> [String] -> [String]
similarStrings s = filter (similar s)
        where
                similar (a:r) (b:s) = if a == b then similar r s else
                                r == s || a:r == s || r == b:s ||
                                case (r, s) of
                                        (x:t, y:u) -> x == b && a == y && t == u
                                        _ -> False
                similar [] [] = True
                similar [] s = length s <= 1
                similar r [] = length r <= 1

