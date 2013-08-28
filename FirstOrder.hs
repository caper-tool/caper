module FirstOrder where
import Prelude hiding (foldl, foldr, elem)
import Data.Foldable
import ProverDatatypes
import qualified Data.Set as Set

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

freeIn :: (Eq v, Foldable a) => v -> FOF a v -> Bool
freeIn v (FOFForAll v' f) = if v == v' then False else freeIn v f
freeIn v (FOFExists v' f) = if v == v' then False else freeIn v f
freeIn v (FOFAnd f1 f2) = freeIn v f1 || freeIn v f2
freeIn v (FOFOr f1 f2) = freeIn v f1 || freeIn v f2
freeIn v (FOFImpl f1 f2) = freeIn v f1 || freeIn v f2
freeIn v (FOFNot f) = freeIn v f
freeIn v (FOFAtom a) = elem v a
freeIn v _ = False

quantifierDepth :: FOF a v -> Int
quantifierDepth (FOFForAll v f) = 1 + quantifierDepth f
quantifierDepth (FOFExists v f) = 1 + quantifierDepth f
quantifierDepth (FOFAnd f1 f2) = max (quantifierDepth f1) (quantifierDepth f2)
quantifierDepth (FOFOr f1 f2) = max (quantifierDepth f1) (quantifierDepth f2)
quantifierDepth (FOFImpl f1 f2) = max (quantifierDepth f1) (quantifierDepth f2)
quantifierDepth (FOFNot f) = quantifierDepth f
quantifierDepth _ = 0

freeVariables :: (Ord v, Foldable a) => FOF a v -> Set.Set v
freeVariables (FOFForAll v f) = Set.delete v (freeVariables f)
freeVariables (FOFExists v f) = Set.delete v (freeVariables f)
freeVariables (FOFAnd f1 f2) = Set.union (freeVariables f1) (freeVariables f2)
freeVariables (FOFOr f1 f2) = Set.union (freeVariables f1) (freeVariables f2)
freeVariables (FOFImpl f1 f2) = Set.union (freeVariables f1) (freeVariables f2)
freeVariables (FOFNot f) = freeVariables f
freeVariables (FOFAtom a) = Set.fromList $ toList a
freeVariables _ = Set.empty
