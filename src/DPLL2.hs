{-# LANGUAGE RankNTypes #-}
module DPLL2 where
import Data.Bits
import qualified Data.Sequence as Seq
import Data.Sequence ((|>), (<|), (><), Seq)
import Data.Foldable
import Prelude hiding (foldl, foldr, mapM, mapM_, foldl1)
import Data.Maybe
import Control.Monad.State hiding (mapM, mapM_)
import Data.Traversable
--import Debug.Trace
import Math.NumberTheory.Logarithms

trace :: String -> a -> a
{-# INLINE trace #-}
trace x y = y

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

instance Show Model where
        show (Model (c, m)) = show (Clause (c, m))

triSat :: Model -> Clause -> Maybe Bool
-- Returns Just True if the clause is satisfied
-- Returns Just False if its negation is satisfied
-- Returns Nothing if it has no valuation in the model
triSat (Model (m,mmask)) (Clause (c,cmask))
        | complement (m `xor` c) .&. (mmask .&. cmask) /= 0 = Just True
        | (complement mmask) .&. cmask /= 0 = Nothing
        | otherwise = Just False

validate :: Model -> [Clause] -> Bool
validate m cs = foldr (\c -> ((Just True == triSat m c) &&)) True cs

watch :: Model -> [Clause] -> a -> a
watch m cs = foldr (\c -> (if (Just False == triSat m c) then error $ "Model violation\n c:" ++ show c ++ "\n m:" ++ show m else id)) id cs

watch' cs m = watch m cs

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

dpll :: MonadPlus m => [Clause] -> m Model
dpll cs = let m = Model (0,0) in dpll' (\x -> id) (purify m cs) [] cs

dpll' :: MonadPlus m => (forall a. Model -> a -> a) -> Model -> [Clause] -> [Clause] -> m Model
dpll' _ m [] [] = return m
dpll' f mdl@(Model (m,mmask)) us (cl@(Clause (c,cmask)) : cs)
        | complement (m `xor` c) .&. (mmask .&. cmask) /= 0 = (trace $ "dropping\n c:" ++ show cl ++ "\n m:" ++ show mdl) $ (f mdl) $ dpll' f mdl us cs
        | (complement mmask) .&. cmask /= 0 = let pcm = (complement mmask) .&. cmask in if popCount pcm == 1 then
                                        -- propagate the unit!
                                        -- Need to check if propagation forces backtracking!
                                        (trace $ "propagating: " ++ show (integerLog2' pcm) ++ "\n m:" ++ show mdl ++ "\n c:" ++ show cl) $ (f $ (Model (m .|. (c .&. pcm), mmask .|. pcm))) $ dpll' f (purify (Model (m .|. (c .&. pcm), mmask .|. pcm)) (us++cs)) [] $! (us ++ cs)
                                else
                                        dpll' f mdl (cl : us) cs
        | otherwise = trace "backtracking" mzero
dpll' f m us [] = (watch m us) $ dpll' f (purify mp us) [] us `mplus` dpll' f (purify mn us) [] us
        where
                (mp, mn) = chooseLiteral m us

purify m cs = m' -- (trace $ "Purify: " ++ show m ++ " ==> " ++ show m' ++ "\nGiven:\n" ++ show cs) m'
        where m' = purify' m cs 0 0

purify' :: Model -> [Clause] -> Integer -> Integer -> Model
purify' (Model (m,mmask)) [] pos neg = Model (m .|. ((complement mmask .&. pos) .&. (pos `xor` neg)), mmask .|. (pos `xor` neg))
purify' m ((Clause (c,cm)):cs) pos neg = purify' m cs (pos .|. (c .&. cm)) (neg .|. (complement c .&. cm))

chooseLiteral :: Model -> [Clause] -> (Model, Model)
-- Pick a litral that occurs in the clauses but not the model
-- Return the model modified with it true and false
chooseLiteral m@(Model (mv, mm)) cs = (trace $ "choosing: " ++ show lit) (Model (setBit mv lit, setBit mm lit), Model (clearBit mv lit, setBit mm lit))
        where
                lit = (trace $ show m) getMax (rankFriends m cs) (candidateLiterals m cs)


getMax :: Ord b => (a -> b) -> [a] -> a
getMax _ [] = error "getMax called with empty list"
getMax r (l : ls) = gm l (r l) ls
        where
                gm best _ [] = best
                gm best bestrank (x : xs) = if r x > bestrank then gm x (r x) xs else gm best bestrank xs

candidateLiterals :: Model -> [Clause] -> [Int]
candidateLiterals (Model (_,mmask)) cs = getBits 0 [] $ complement mmask .&. foldr (\(Clause (_,cm)) -> (cm .|.)) 0 cs
        where
                getBits x l 0 = l
                getBits x l n = getBits (x+1) (if n `testBit` 0 then x : l else l) (shiftR n 1)

rankCommon :: Model -> [Clause] -> Int -> Int
rankCommon _ cs b = rc cs 0
        where
                rc [] n = n
                rc ((Clause (_, cm)) : cr) n = rc cr $! (if testBit cm b then n + 1 else n)

rankFriends :: Model -> [Clause] -> Int -> Int
rankFriends (Model (_,mm)) cs b = popCount $ mm .&. rf cs 0
        where
                rf [] n = n
                rf ((Clause (_,cm)) : cr) n = rf cr $! if testBit cm b then n .|. cm else n

rankCF m cs b = rankFriends m cs b * rankCommon m cs b

rankPolarity :: Model -> [Clause] -> Int -> Int
rankPolarity _ cs b = (uncurry max) $ rp cs (0, 0)
        where
                rp [] r = r
                rp ((Clause (cc, cm)) : cr) (n,m) = rp cr $! (if testBit cm b then if testBit cc b then (n+1,m) else (n,m+1) else (n,m))

rankUnfriends m cs b = - rankFriends m cs b

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
{-
toClause :: [(Bool,Integer)] -> Clause
toClause = Clause . (tc' 0 0)
        where
                tc' mod mask [] = (mod,mask)
                tc' mod mask ((p,i) : cs) = let ii = fromInteger i - 1 in
                        if testBit mask ii then
                                (0,0) 
                        else
                                tc' ((if p then setBit else clearBit) mod ii)
                                        (setBit mask ii) cs
-}
