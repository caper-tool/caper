
module Caper.Provers.Permissions.Internal (permCheckBigInt, permCheckTree) where
import Data.List
import Data.Maybe
import Control.Parallel.Strategies
import Data.Bits

import qualified Caper.ProverDatatypes as PD


class PermModel p where
        emptyModel :: p
        isEmptyIntersection :: p -> [(Int,Bool)] -> Bool
        splitModel :: p -> [p]


combine :: (a -> b -> c) -> [a] -> [b] -> [c]
combine f xs l2 = foldr (\ x -> (++) (map (f x) l2)) [] xs
{-
combine f [] l2 = []
combine f (x : xs) l2 = map (f x) l2 ++ combine f xs l2
-}

data EvalTree = ETSome | ETNone | ETBranch EvalTree EvalTree

instance Show EvalTree where
        show ETSome = "@"
        show ETNone = "."
        show (ETBranch t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
        
evalEmptyInters :: EvalTree -> [(Int,Bool)] -> Bool
evalEmptyInters t l = case squishSortedIntersectionList (sort l) of
                Nothing -> True
                Just l' -> evalEmptyIntersections t l' 0

squishSortedIntersectionList :: [(Int,Bool)] -> Maybe [(Int,Bool)]
squishSortedIntersectionList [] = Just []
squishSortedIntersectionList [x] = Just [x]
squishSortedIntersectionList ((d1, t1) : (d2, t2) : xs) = if d1 == d2 then
        if t1 == t2 then squishSortedIntersectionList ((d2, t2) : xs) else Nothing
        else fmap ((d1, t1) :) (squishSortedIntersectionList ((d2, t2) : xs))

evalEmptyIntersections :: EvalTree -> [(Int,Bool)] -> Int -> Bool
evalEmptyIntersections ETNone _ _ = True
evalEmptyIntersections _ [] _ = False
evalEmptyIntersections ETSome _ _ = error "evalEmptyIntersections: Tree does not evaluate all variables"
evalEmptyIntersections (ETBranch t1 t2) l@((dx,tx):xs) d
        | dx > d        = evalEmptyIntersections t1 l (d+1) && evalEmptyIntersections t2 l (d+1)
        | tx            = evalEmptyIntersections t2 xs (d+1)
        | otherwise     = evalEmptyIntersections t1 xs (d+1)

etSplits :: EvalTree -> [EvalTree]
etSplits ETSome = [ETBranch ETSome ETSome, ETBranch ETSome ETNone, ETBranch ETNone ETSome]
etSplits ETNone = [ETNone]
etSplits (ETBranch et1 et2) = combine ETBranch (etSplits et1) (etSplits et2)

instance PermModel EvalTree where
        emptyModel = ETSome
        isEmptyIntersection = evalEmptyInters
        splitModel = etSplits


data IntegerTree = ITree !Integer !Int deriving (Eq, Ord, Show)

mask 0 depth = 2 ^ (2 ^ (depth - 1)) - 1
mask n depth = let m = mask (n - 1) (depth - 1) in m .|. shiftL m (2 ^ (depth - 1))


instance PermModel IntegerTree where
        emptyModel = ITree 1 0
        isEmptyIntersection (ITree v d) l = 0 == foldl (.&.) v (map (\(n,c) -> if c then complement (mask (d - n - 1) d) else mask (d - n - 1) d) l)
        splitModel (ITree v d) = map (\n -> ITree n (d+1)) (bitsy 0)
                where
                        bitsy bit = if bit >= 2^d then [0]
                                else let bitsn = bitsy (bit + 1) in
                                if testBit v bit then
                                        concat [ [setBit n bit, setBit n (bit + 2^d), setBit (setBit n (bit + 2^d)) bit] | n <- bitsn ]
                                else bitsn
                                        


-- Permissions with expressions

data PermExpr = PEFull | PEZero | PEVar Int | PESum PermExpr PermExpr | PECompl PermExpr
data PermAtom = PAEqual PermExpr PermExpr | PADisjoint PermExpr PermExpr
data PermFormula = PFFalse | PFTrue
                | PFAtom PermAtom
                | PFNot PermFormula
                | PFAnd PermFormula PermFormula
                | PFOr PermFormula PermFormula
                | PFImpl PermFormula PermFormula
                | PFAll PermFormula
                | PFEx PermFormula

instance Show PermExpr where
        show PEFull = "1"
        show PEZero = "0"
        show (PEVar n) = "[" ++ show n ++ "]"
        show (PESum pe1 pe2) = "(" ++ show pe1 ++ " + " ++ show pe2 ++ ")"
        show (PECompl pe) = "(1 - " ++ show pe ++ ")"
instance Show PermAtom where
        show (PAEqual e1 e2) = show e1 ++ " = " ++ show e2
        show (PADisjoint e1 e2) = show e1 ++ " # " ++ show e2

instance Show PermFormula where
        show PFFalse = "_|_"
        show PFTrue = "T"
        show (PFAtom a) = show a
        show (PFNot f) = "¬ " ++ show f
        show (PFAnd f1 f2) = "(" ++ show f1 ++ " /\\ " ++ show f2 ++ ")"
        show (PFOr f1 f2) = "(" ++ show f1 ++ " \\/ " ++ show f2 ++ ")"
        show (PFImpl f1 f2) = "(" ++ show f1 ++ " => " ++ show f2 ++ ")"
        show (PFAll f1) = "(A)(" ++ show f1 ++ ")"
        show (PFEx f1) = "(E)(" ++ show f1 ++ ")"


toPermExpr :: (a -> Int) -> PD.PermissionExpression a -> PermExpr
toPermExpr s PD.PEFull = PEFull
toPermExpr s PD.PEZero = PEZero
toPermExpr s (PD.PEVar x) = PEVar (s x)
toPermExpr s (PD.PESum e1 e2) = PESum (toPermExpr s e1) (toPermExpr s e2)
toPermExpr s (PD.PECompl e) = PECompl (toPermExpr s e)

toPermAtom :: (a -> Int) -> PD.PermissionAtomic a -> PermAtom
toPermAtom s (PD.PAEq e1 e2) = PAEqual (toPermExpr s e1) (toPermExpr s e2)
toPermAtom s (PD.PADis e1 e2) = PADisjoint (toPermExpr s e1) (toPermExpr s e2)

toPermFormula :: (Eq a) => (a -> Int) -> PD.FOF PD.PermissionAtomic a -> PermFormula
toPermFormula s (PD.FOFForAll v f') = PFAll (toPermFormula (\x -> if x == v then 0 else s x + 1) f')
toPermFormula s (PD.FOFExists v f') = PFEx (toPermFormula (\x -> if x == v then 0 else s x + 1) f')
toPermFormula s (PD.FOFAtom a) = PFAtom $ toPermAtom s a
toPermFormula s (PD.FOFAnd f1 f2) = PFAnd (toPermFormula s f1) (toPermFormula s f2)
toPermFormula s (PD.FOFOr f1 f2) = PFOr (toPermFormula s f1) (toPermFormula s f2)
toPermFormula s (PD.FOFImpl f1 f2) = PFImpl (toPermFormula s f1) (toPermFormula s f2)
toPermFormula s (PD.FOFNot f) = PFNot (toPermFormula s f)
toPermFormula _ PD.FOFFalse = PFFalse
toPermFormula _ PD.FOFTrue = PFTrue

toPermSentence :: PD.FOF PD.PermissionAtomic String -> PermFormula
toPermSentence f = toPermFormula (\x -> error $ "toPermSentence: Variable " ++ x ++ " occurs free in the formula:\n" ++ show f) f



-- testpf1 = PFAll $ PFImpl (PFEx $ PFEx $ PFAnd (PFAtom $ PAEqual (PESum (PEVar 0) (PEVar 1)) (PEVar 2)) (PFAtom $ PAEqual (PEVar 0) (PEVar 1))) (PFAtom $ PADisjoint (PEVar 0) PEFull)

formulaEvalBigInt :: PermFormula -> Bool
formulaEvalBigInt = formulaEvalEnv 0 (emptyModel :: IntegerTree)

formulaEvalTree :: PermFormula -> Bool
formulaEvalTree = formulaEvalEnv 0 (emptyModel :: EvalTree)


formulaEvalEnv :: (PermModel p) => Int -> p -> PermFormula -> Bool
formulaEvalEnv _ _ PFFalse = False
formulaEvalEnv _ _ PFTrue = True
formulaEvalEnv d et (PFNot f) = not $ formulaEvalEnv d et f
formulaEvalEnv d et (PFAnd f1 f2) = formulaEvalEnv d et f1 && formulaEvalEnv d et f2
formulaEvalEnv d et (PFOr f1 f2) = formulaEvalEnv d et f1 || formulaEvalEnv d et f2
formulaEvalEnv d et (PFImpl f1 f2) = not (formulaEvalEnv d et f1) || formulaEvalEnv d et f2
formulaEvalEnv d et (PFAll f) = and (parMap rseq (\e -> formulaEvalEnv (d+1) e f) (splitModel et))
formulaEvalEnv d et (PFEx f) = or (parMap rseq (\e -> formulaEvalEnv (d+1) e f) (splitModel et))
formulaEvalEnv d et (PFAtom a) = atomEvalEnv d et a

atomEvalEnv :: (PermModel p) => Int -> p -> PermAtom -> Bool
atomEvalEnv d et (PAEqual pe1 pe2) = let pc1 = exprToComb pe1 in
                                let pc2 = exprToComb pe2 in
                                        isPCEmpty d et (exprDisjCombs pe1) &&
                                        isPCEmpty d et (exprDisjCombs pe2) &&
                                        isPCEmpty d et (PCInter pc1 (PCCompl pc2)) &&
                                        isPCEmpty d et (PCInter (PCCompl pc1) pc2)
atomEvalEnv d et (PADisjoint pe1 pe2) = isPCEmpty d et (exprDisjCombs pe1) && isPCEmpty d et (exprDisjCombs pe2) &&
                                        isPCEmpty d et (PCInter (exprToComb pe1) (exprToComb pe2))

exprToComb :: PermExpr -> PermComb
exprToComb PEFull = PCPrim PPFull
exprToComb PEZero = PCPrim PPZero
exprToComb (PEVar n) = PCPrim (PPVar n)
exprToComb (PESum pe1 pe2) = PCUnion (exprToComb pe1) (exprToComb pe2)
exprToComb (PECompl pe) = PCCompl (exprToComb pe)

exprDisjCombs :: PermExpr -> PermComb
-- Find a permission combination that is zero exactly when all sums are disjoint
exprDisjCombs (PESum pe1 pe2) = PCUnion (PCInter (exprToComb pe1) (exprToComb pe2)) $
                                PCUnion (exprDisjCombs pe1) (exprDisjCombs pe2)
exprDisjCombs (PECompl pe) = exprDisjCombs pe
exprDisjCombs _ = PCPrim PPZero

data PermPrim = PPFull | PPZero | PPVar Int 
data PermComb = PCPrim PermPrim | PCCompl PermComb | PCUnion PermComb PermComb | PCInter PermComb PermComb

normalise :: PermComb -> [[(PermPrim,Bool)]]
normalise (PCPrim pp) = [[(pp, False)]]
normalise (PCUnion pc1 pc2) = normalise pc1 ++ normalise pc2
normalise (PCInter pc1 pc2) = combine (++) (normalise pc1) (normalise pc2)
normalise (PCCompl pc) = case pc of
                        (PCPrim pp) -> [[(pp, True)]]
                        (PCUnion pc1 pc2) -> normalise $ PCInter (PCCompl pc1) (PCCompl pc2)
                        (PCInter pc1 pc2) -> normalise $ PCUnion (PCCompl pc1) (PCCompl pc2)
                        (PCCompl pc') ->  normalise pc'

simplify :: [[(PermPrim,Bool)]] -> [[(Int,Bool)]]
simplify = mapMaybe inter_simplify
        where
                inter_simplify :: [(PermPrim,Bool)] -> Maybe [(Int,Bool)]
                inter_simplify [] = return []
                inter_simplify ((pp,b) : xs) = case pp of
                        PPFull -> if b then Nothing else inter_simplify xs
                        PPZero -> if b then inter_simplify xs else Nothing
                        (PPVar n) -> do
                                xs' <- inter_simplify xs
                                return $ (n,b) : xs'

correctIndexes :: Int -> [[(Int,Bool)]] -> [[(Int,Bool)]]
correctIndexes d = map (map ci)
        where
                ci (i,b) = (d - i - 1, b)

isNPCEmpty :: (PermModel p) => p -> [[(Int,Bool)]] -> Bool
isNPCEmpty et = all (isEmptyIntersection et)

isPCEmpty :: (PermModel p) => Int -> p -> PermComb -> Bool
isPCEmpty d et = isNPCEmpty et . correctIndexes d . simplify . normalise

-- |Check a permission assertion using an Integer representation of binary trees.
permCheckBigInt :: PD.PermissionsProver
permCheckBigInt f = return $! Just $! formulaEvalBigInt $ toPermSentence f

-- |Check a permission assertion using a binary-tree representation.
permCheckTree :: PD.PermissionsProver
permCheckTree f = return $! Just $! formulaEvalTree $ toPermSentence f
