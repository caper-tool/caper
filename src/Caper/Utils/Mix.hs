module Caper.Utils.Mix where

import qualified Data.Set as Set

-- |Given a binary operation and two sets, return a set consisting of the result
-- of the operation applied to every pair of element from the first set and
-- element of the second.
mixWith :: (Ord a, Ord b, Ord c) => (a -> b -> c) -> Set.Set a -> Set.Set b -> Set.Set c
mixWith op s1 s2 = Set.unions $ Set.toList $ Set.map (\x -> Set.map (op x) s2) s1

-- |Given a binary operation and two lists, return a list consisting of the 
-- result of the operation applied to every pair of element from the first list
-- and element of the second.
listMixWith :: (a -> b -> c) -> [a] -> [b] -> [c]
listMixWith op l1 l2 = concatMap (\ x -> map (op x) l2) l1
