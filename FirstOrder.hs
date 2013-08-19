
import Prelude hiding (foldl, foldr, elem)
import Data.Foldable
import ProverDatatypes

simplify :: (Foldable a, Eq v) => FOF a v -> FOF a v
simplify (FOFForAll v f)
        | elem v f1 = case f of
                (FOFNot f') -> FOFNot $ simplify $ FOFExists v f'
                (FOFAnd f1 f2) -> FOFAnd (simplify $ FOFForAll v f1) (simplify $ FOFForAll v f2)
                (FOFOr f1 f2) -> case (elem v f1, elem v f2) of
                        (True, False) -> FOFOr (simplify $ FOFForAll v f1) (simplify f2)
                        (False, True) -> FOFOr (simplify f1) (simplify $ FOFForAll v f2)
                        _ -> FOFForAll v $ FOFOr (simplify f1) (simplify f2)
                (FOFImpl f1 f2) -> case (elem v f1, elem v2 f2) of
                        (True, False) -> FOFImpl (simplify $ FOFExists v f1) (simplify f2)
                        (False, True) -> FOFImpl (simplify f1) (simplify $ FOFForAll f2)
                        _ -> FOFImpl (simplify $ FOFExists v f1) (simplify $ FOFForAll v f2)
                _ -> let f' = simplify f in case f' of
                        (FOFForAll v' f'') -> FOFForAll v' (simplify $ FOFForAll v f'')
                        (FOFExists v' f'') -> FOFForAll v f'
                        _ -> if f == f' then FOFForAll v f else simplify $ FOFForAll v f'
        | otherwise = simplify f
simplify (FOFExists v f)
        | elem v f1 = case f of
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
