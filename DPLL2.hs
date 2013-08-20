import Data.Bits
import qualified Data.Sequence as Seq
import Data.Sequence ((|>), (<|), (><), Seq)
import Control.Monad.State
import Data.Foldable
import Prelude hiding (foldl, foldr, mapM, mapM_)
import Data.Maybe
import Debug.Trace
import Control.Monad.State hiding (mapM, mapM_)
import Data.Traversable

newtype Model = Model (Integer, Integer)

-- A clause is a pair of bitvectors.
-- The first indicates whether a literal should be interpreted
-- positively or negatively.  The second indicates whether
-- that literal is included in the clause.
-- Any literal that is not set in the mask MUST be unset in the
-- interpretation.
newtype Clause = Clause (Integer, Integer)


instance Show Clause where
        show (Clause (c, m)) = show' c m
                where
                        show' _ 0 = ""
                        show' cx mx = (if testBit mx 0 then
                                if testBit cx 0 then '+' else '-'
                                else '*') : show' (shift cx (-1)) (shift mx (-1))

triSat :: Model -> Clause -> Maybe Bool
-- Returns Just True if the clause is satisfied
-- Returns Just False if its negation is satisfied
-- Returns Nothing if it has no valuation in the model
triSat (Model (m,mmask)) (Clause (c,cmask))
        | complement (m `xor` c) .&. (mmask .&. cmask) /= 0 = Just True
        | (complement mmask) .&. cmask /= 0 = Nothing
        | otherwise = Just False

propagateUnits :: Model -> Seq Clause -> Model
propagateUnits m s = propagateUnits m (Seq.filter (\x -> Nothing == triSat m x) s)

propagateUnits' :: Model -> Seq Clause -> Model
propagateUnits' m s = execState (mapM_ pu s) m
        where
                pu :: Clause -> State Model ()
                pu (Clause (c, cmask)) = do
                        (Model (m, mmask)) <- get
                        let pcm = cmask .&. complement mmask
                        let pc = popCount pcm
                        if pc == 1 then
                                put $ Model (m .|. (c .&. pcm), mmask .|. pcm)
                        else
                                return ()

dpll' :: Model -> [Clause] -> [Clause] -> Maybe Model
dpll' m [] [] = return m
dpll' mdl@(Model (m,mmask)) us (cl@(Clause (c,cmask)) : cs)
        | complement (m `xor` c) .&. (mmask .&. cmask) /= 0 = dpll' mdl us cs
        | (complement mmask) .&. cmask /= 0 = let pcm = (complement mmask) .&. cmask in if popCount pcm == 1 then
                                        -- propagate the unit!
                                        dpll' (Model (m .|. (c .&. pcm), mmask .|. pcm)) [] $! (us ++ cs)
                                else
                                        dpll' mdl (cl : us) cs
        | otherwise = mzero
dpll' m us [] = dpll' mp [] us `mplus` dpll' mn [] us
        where
                m' = purify m us 0 0 in
                (mp, mn) = chooseLiteral m' us

purify :: Model -> [Clause] -> Integer -> Integer -> Model
purify (Model (m,mmask)) [] pos neg = Model (m .|. (pos .&. (pos `xor` neg)), mmask .|. (pos `xor` neg))
purify m ((Clause (c,cm)):cs) pos neg = purify m cs (pos .|. (c .&. cm)) (neg .|. (complement c .&. cm))

chooseLiteral :: Model -> [Clause] -> (Model, Model)
-- Pick a litral that 




data Proposition a = Prop a
                | PAnd (Proposition a) (Proposition a)
                | POr (Proposition a) (Proposition a)
                | PNot (Proposition a)
                deriving (Eq, Ord)
instance Show a => Show (Proposition a) where
        show (Prop a) = show a
        show (PAnd p1 p2) = "(" ++ show p1 ++ " /\\ " ++ show p2 ++ ")"
        show (POr p1 p2) = "(" ++ show p1 ++ " \\/ " ++ show p2 ++ ")"
        show (PNot p) = "~" ++ show p

clauseOrS :: Clause -> Clause -> Seq Clause
-- Return nothing if the clauses contain a literal and its negation
-- Otherwise, return a clause that is satisfied exactly when either of the clauses is
clauseOrS (Clause (c1, m1)) (Clause (c2, m2))
        | (c1 `xor` c2) .&. (m1 .&. m2) == 0 = Seq.singleton $ Clause (c1 .|. c2, m1 .|. m2)
        | otherwise = Seq.empty


mixWithS :: (a -> b -> Seq c) -> Seq a -> Seq b -> Seq c
mixWithS f as bs = foldMap (\a -> foldMap (f a) bs) as

toCNF :: Eq a => Proposition a -> (Seq a, Seq Clause)
toCNF = toCNF' Seq.empty where
        toCNF' s (Prop p) = case Seq.elemIndexL p s of
                Just n -> (s, Seq.singleton $ Clause (bit n, bit n))
                Nothing -> (s |> p, let b = bit (Seq.length s) in Seq.singleton $ Clause (b, b))
        toCNF' s (PNot (Prop p)) = case Seq.elemIndexL p s of
                Just n -> (s, Seq.singleton $ Clause (0, bit n))
                Nothing -> (s |> p, Seq.singleton $ Clause (0,bit (Seq.length s)))
        toCNF' s (PNot (PAnd p1 p2)) = toCNF' s (POr (PNot p1) (PNot p2))
        toCNF' s (PNot (POr p1 p2)) = toCNF' s (PAnd (PNot p1) (PNot p2))
        toCNF' s (PNot (PNot p)) = toCNF' s p
        toCNF' s (PAnd p1 p2) = let (s1, c1) = toCNF' s p1 in
                                let (s2, c2) = toCNF' s1 p2 in
                                (s2, c1 >< c2)
        toCNF' s (POr p1 p2) = let (s1, c1) = toCNF' s p1 in
                                let (s2, c2) = toCNF' s1 p2 in
                                (s2, mixWithS (clauseOrS) c1 c2)

