{-# LANGUAGE FlexibleContexts #-}
module Caper.FirstOrder(
    simplify,
    rewriteFOF,
    simplR,
    pNormalise,
    quantifierDepth,
    sentence,
    boundIn
) where
import Prelude hiding (foldl, foldr, elem, notElem)
import Data.Foldable
import qualified Data.Set as Set

import Caper.ProverDatatypes

simplify :: (Foldable a, Eq v, Eq (a v)) => FOF a v -> FOF a v
simplify (FOFForAll v f)
        | elem v f = case f of
                (FOFNot f') -> FOFNot $ simplify $ FOFExists v f'
                (FOFAnd f1 f2) -> FOFAnd (simplify $ FOFForAll v f1) (simplify $ FOFForAll v f2)
                (FOFOr f1 f2) -> case (elem v f1, elem v f2) of
                        (True, False) -> FOFOr (simplify $ FOFForAll v f1) (simplify f2)
                        (False, True) -> FOFOr (simplify f1) (simplify $ FOFForAll v f2)
                        _ -> FOFForAll v $ FOFOr (simplify f1) (simplify f2)
                (FOFImpl f1 f2) -> case (elem v f1, elem v f2) of
                        (True, False) -> FOFImpl (simplify $ FOFExists v f1) (simplify f2)
                        (False, True) -> FOFImpl (simplify f1) (simplify $ FOFForAll v f2)
                        _ -> FOFForAll v $ FOFImpl (simplify f1) (simplify f2)
                _ -> let f' = simplify f in case f' of
                        (FOFForAll v' f'') -> FOFForAll v' (simplify $ FOFForAll v f'')
                        (FOFExists v' f'') -> FOFForAll v f'
                        _ -> if f == f' then FOFForAll v f else simplify $ FOFForAll v f'
        | otherwise = simplify f
simplify (FOFExists v f)
        | elem v f = case f of
                (FOFNot f') -> FOFNot $ simplify $ FOFForAll v f'
                (FOFOr f1 f2) -> FOFOr (simplify $ FOFExists v f1) (simplify $ FOFExists v f2)
                (FOFImpl f1 f2) -> FOFImpl (simplify $ FOFForAll v f1) (simplify $ FOFExists v f2)
                (FOFAnd f1 f2) -> case (elem v f1, elem v f2) of
                        (True, False) -> FOFAnd (simplify $ FOFExists v f1) (simplify f2)
                        (False, True) -> FOFAnd (simplify f1) (simplify $ FOFExists v f2)
                        _ -> FOFExists v $ FOFAnd (simplify f1) (simplify f2)
                _ -> let f' = simplify f in case f' of
                        (FOFForAll v' f'') -> FOFExists v f'
                        (FOFExists v' f'') -> FOFExists v' (simplify $ FOFExists v f'')
                        _ -> if f == f' then FOFExists v f else simplify $ FOFExists v f'
        | otherwise = simplify f
simplify (FOFAnd f1 f2) = FOFAnd (simplify f1) (simplify f2)
simplify (FOFOr f1 f2) = FOFOr (simplify f1) (simplify f2)
simplify (FOFImpl f1 f2) = FOFImpl (simplify f1) (simplify f2)
simplify (FOFNot f1) = FOFNot (simplify f1)
simplify x = x

unmaybe :: (a -> Maybe a) -> (a -> a) -> a -> a
unmaybe f g x = case f x of
                Just y -> g y
                Nothing -> x

rewriteFOF :: (FOF a v -> Maybe (FOF a v)) -> FOF a v -> FOF a v
rewriteFOF f = unmaybe f (rewriteFOF f) . business
        where
                business (FOFForAll v p) = FOFForAll v (rewriteFOF f p)
                business (FOFExists v p) = FOFExists v (rewriteFOF f p)
                business (FOFAnd p1 p2) = FOFAnd (rewriteFOF f p1) (rewriteFOF f p2)
                business (FOFOr p1 p2) = FOFOr (rewriteFOF f p1) (rewriteFOF f p2)
                business (FOFImpl p1 p2) = FOFImpl (rewriteFOF f p1) (rewriteFOF f p2)
                business (FOFNot p) = FOFNot (rewriteFOF f p)
                business z = z

simplR :: FOF a v -> Maybe (FOF a v)
simplR (FOFAnd FOFTrue x) = Just x
simplR (FOFAnd x FOFTrue) = Just x
simplR (FOFAnd FOFFalse x) = Just FOFFalse
simplR (FOFAnd x FOFFalse) = Just FOFFalse
simplR (FOFOr FOFTrue x) = Just FOFTrue
simplR (FOFOr x FOFTrue) = Just FOFTrue
simplR (FOFOr FOFFalse x) = Just x
simplR (FOFOr x FOFFalse) = Just x
simplR (FOFImpl FOFTrue x) = Just x
simplR (FOFImpl x FOFTrue) = Just FOFTrue
simplR (FOFImpl FOFFalse x) = Just FOFTrue
simplR (FOFImpl x FOFFalse) = Just (FOFNot x)
simplR _ = Nothing




boundIn :: (Eq v, Foldable a) => v -> FOF a v -> Bool
boundIn v (FOFForAll v' f) = v == v' || boundIn v f
boundIn v (FOFExists v' f) = v == v' || boundIn v f
boundIn v (FOFAnd f1 f2) = boundIn v f1 || boundIn v f2
boundIn v (FOFOr f1 f2) = boundIn v f1 || boundIn v f2
boundIn v (FOFImpl f1 f2) = boundIn v f1 || boundIn v f2
boundIn v (FOFNot f) = boundIn v f
boundIn v (FOFAtom a) = elem v a
boundIn v _ = False

sentence :: (Eq v, Ord v, Foldable a) => FOF a v -> Bool
sentence = sentence' Set.empty
        where
                sentence' s (FOFForAll v a) = sentence' (Set.insert v s) a
                sentence' s (FOFExists v a) = sentence' (Set.insert v s) a
                sentence' s FOFTrue = True
                sentence' s FOFFalse = True
                sentence' s (FOFAnd f1 f2) = sentence' s f1 && sentence' s f2
                sentence' s (FOFOr f1 f2) = sentence' s f1 && sentence' s f2
                sentence' s (FOFImpl f1 f2) = sentence' s f1 && sentence' s f2
                sentence' s (FOFNot f) = sentence' s f
                sentence' s (FOFAtom a) = foldr (\x -> (x `elem` s &&)) True a

quantifierDepth :: FOF a v -> Int
quantifierDepth (FOFForAll v f) = 1 + quantifierDepth f
quantifierDepth (FOFExists v f) = 1 + quantifierDepth f
quantifierDepth (FOFAnd f1 f2) = max (quantifierDepth f1) (quantifierDepth f2)
quantifierDepth (FOFOr f1 f2) = max (quantifierDepth f1) (quantifierDepth f2)
quantifierDepth (FOFImpl f1 f2) = max (quantifierDepth f1) (quantifierDepth f2)
quantifierDepth (FOFNot f) = quantifierDepth f
quantifierDepth _ = 0

-- | Rewrite a first-order formula to prenex-normal form (i.e. all
-- quantifiers on the outside).  (This assumes that all sorts are inhabited.)
pNormalise :: (Functor a, Foldable a, Eq v, Eq (a v), Refreshable v) => FOF a v -> FOF a v
pNormalise (FOFForAll v f) = FOFForAll v (pNormalise f)
pNormalise (FOFExists v f) = FOFExists v (pNormalise f)
pNormalise (FOFAnd f1 f2) = normAO FOFAnd (pNormalise f1) (pNormalise f2)
pNormalise (FOFOr f1 f2) = normAO FOFOr (pNormalise f1) (pNormalise f2)
pNormalise (FOFImpl f1 f2) = normImpl (pNormalise f1) (pNormalise f2)
pNormalise (FOFNot f) = normNot (pNormalise f)
pNormalise f = f

normAO :: (Eq v, Functor t, Foldable t, Refreshable v) =>
            (FOF t v -> FOF t v -> FOF t v) -> FOF t v -> FOF t v -> FOF t v
normAO o (FOFForAll v f1) f2 = let (v', f1') = frsh v f1 f2 in
        FOFForAll v' (normAO o f1' f2)
normAO o (FOFExists v f1) f2 = let (v', f1') = frsh v f1 f2 in
        FOFExists v' (normAO o f1' f2)
normAO o f1 (FOFForAll v f2) = let (v', f2') = frsh v f2 f1 in
        FOFForAll v' (normAO o f1 f2')
normAO o f1 (FOFExists v f2) = let (v', f2') = frsh v f2 f1 in
        FOFExists v' (normAO o f1 f2')
normAO o f1 f2 = o f1 f2

normImpl :: (Eq v, Functor t, Foldable t, Refreshable v) =>
            FOF t v -> FOF t v -> FOF t v
normImpl (FOFForAll v f1) f2 = let (v', f1') = frsh v f1 f2 in
        FOFExists v' (normImpl f1' f2)
normImpl (FOFExists v f1) f2 = let (v', f1') = frsh v f1 f2 in
        FOFForAll v' (normImpl f1' f2)
normImpl f1 (FOFForAll v f2) = let (v', f2') = frsh v f2 f1 in
        FOFForAll v' (normImpl f1 f2')
normImpl f1 (FOFExists v f2) = let (v', f2') = frsh v f2 f1 in
        FOFExists v' (normImpl f1 f2')
normImpl f1 f2 = FOFImpl f1 f2

normNot :: FOF a v -> FOF a v
normNot (FOFForAll v f) = FOFExists v (normNot f)
normNot (FOFExists v f) = FOFForAll v (normNot f)
normNot f = FOFNot f

-- | Rename a bound variable to avoid capture.  Returns the new variable and the
-- bound formula with the variable renamed.
frsh :: (Functor a, Foldable a, Eq v, Refreshable v) =>
        v -- ^The variable to rename
        -> FOF a v -- ^The formula in which it is bound
        -> FOF a v -- ^The formula in which it is not bound, and should not be captured
        -> (v, FOF a v)
frsh v f1 f2
        | not (v `freeIn` f2) = (v, f1)
        | otherwise = let v' = head [x | x <- freshen v, x `notElem` f1, not (x `freeIn` f2)] in
                (v', fmap (\vv -> if vv == v then v' else vv) f1)
