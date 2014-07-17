
module Permissions2 (permCheckBigInt) where
import Data.List
import Data.Maybe
import Control.Parallel.Strategies
import qualified ProverDatatypes as PD
import Data.Bits

class PermModel p where
        emptyModel :: p
        isEmptyIntersection :: p -> [(Int,Bool)] -> Bool
        splitModel :: p -> [p]


combine :: (a -> b -> c) -> [a] -> [b] -> [c]
combine f [] l2 = []
combine f (x : xs) l2 = map (f x) l2 ++ combine f xs l2

data EvalTree = ETSome | ETNone | ETBranch EvalTree EvalTree

instance Show EvalTree where
        show ETSome = "@"
        show ETNone = "."
        show (ETBranch t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
        
eval_empty_inters :: EvalTree -> [(Int,Bool)] -> Bool
eval_empty_inters t l = case squish_sorted_intersection_list (sort l) of
                Nothing -> True
                Just l' -> eval_empty_intersections t l' 0

squish_sorted_intersection_list :: [(Int,Bool)] -> Maybe [(Int,Bool)]
squish_sorted_intersection_list [] = Just []
squish_sorted_intersection_list [x] = Just [x]
squish_sorted_intersection_list ((d1, t1) : (d2, t2) : xs) = if d1 == d2 then
        if t1 == t2 then squish_sorted_intersection_list ((d2, t2) : xs) else Nothing
        else fmap ((d1, t1) :) (squish_sorted_intersection_list ((d2, t2) : xs))

eval_empty_intersections :: EvalTree -> [(Int,Bool)] -> Int -> Bool
eval_empty_intersections ETNone _ _ = True
eval_empty_intersections _ [] _ = False
eval_empty_intersections ETSome _ _ = error "eval_empty_intersections: Tree does not evaluate all variables"
eval_empty_intersections (ETBranch t1 t2) l@((dx,tx):xs) d = if dx > d
        then eval_empty_intersections t1 l (d+1) && eval_empty_intersections t2 l (d+1)
        else if tx then -- True indicates use the complement
                eval_empty_intersections t2 xs (d+1)
                else eval_empty_intersections t1 xs (d+1)

et_splits :: EvalTree -> [EvalTree]
et_splits ETSome = [ETBranch ETSome ETSome, ETBranch ETSome ETNone, ETBranch ETNone ETSome]
et_splits ETNone = [ETNone]
et_splits (ETBranch et1 et2) = combine ETBranch (et_splits et1) (et_splits et2)

instance PermModel EvalTree where
        emptyModel = ETSome
        isEmptyIntersection = eval_empty_inters
        splitModel = et_splits


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

pf_eval :: PermFormula -> Bool
pf_eval = pf_eval_env 0 (emptyModel :: IntegerTree)

pf_eval_env :: (PermModel p) => Int -> p -> PermFormula -> Bool
pf_eval_env _ _ PFFalse = False
pf_eval_env _ _ PFTrue = True
pf_eval_env d et (PFNot f) = not $ pf_eval_env d et f
pf_eval_env d et (PFAnd f1 f2) = pf_eval_env d et f1 && pf_eval_env d et f2
pf_eval_env d et (PFOr f1 f2) = pf_eval_env d et f1 || pf_eval_env d et f2
pf_eval_env d et (PFImpl f1 f2) = if pf_eval_env d et f1 then pf_eval_env d et f2 else True
pf_eval_env d et (PFAll f) = foldl (&&) True (parMap rseq (\e -> pf_eval_env (d+1) e f) (splitModel et))
pf_eval_env d et (PFEx f) = foldl (||) False (parMap rseq (\e -> pf_eval_env (d+1) e f) (splitModel et))
pf_eval_env d et (PFAtom a) = pa_eval_env d et a

pa_eval_env :: (PermModel p) => Int -> p -> PermAtom -> Bool
pa_eval_env d et (PAEqual pe1 pe2) = let pc1 = pe_to_pc pe1 in
                                let pc2 = pe_to_pc pe2 in
                                        pc_empty d et (pe_disj_combs pe1) &&
                                        pc_empty d et (pe_disj_combs pe2) &&
                                        pc_empty d et (PCInter pc1 (PCCompl pc2)) &&
                                        pc_empty d et (PCInter (PCCompl pc1) pc2)
pa_eval_env d et (PADisjoint pe1 pe2) = pc_empty d et (pe_disj_combs pe1) && pc_empty d et (pe_disj_combs pe2) &&
                                        pc_empty d et (PCInter (pe_to_pc pe1) (pe_to_pc pe2))

pe_to_pc :: PermExpr -> PermComb
pe_to_pc PEFull = PCPrim PPFull
pe_to_pc PEZero = PCPrim PPZero
pe_to_pc (PEVar n) = PCPrim (PPVar n)
pe_to_pc (PESum pe1 pe2) = PCUnion (pe_to_pc pe1) (pe_to_pc pe2)
pe_to_pc (PECompl pe) = PCCompl (pe_to_pc pe)

pe_disj_combs :: PermExpr -> PermComb
-- Find a permission combination that is zero exactly when all sums are disjoint
pe_disj_combs (PESum pe1 pe2) = PCUnion (PCInter (pe_to_pc pe1) (pe_to_pc pe2)) $
                                PCUnion (pe_disj_combs pe1) (pe_disj_combs pe2)
pe_disj_combs (PECompl pe) = pe_disj_combs pe
pe_disj_combs _ = PCPrim PPZero

data PermPrim = PPFull | PPZero | PPVar Int 
data PermComb = PCPrim PermPrim | PCCompl PermComb | PCUnion PermComb PermComb | PCInter PermComb PermComb

pc_normalise :: PermComb -> [[(PermPrim,Bool)]]
pc_normalise (PCPrim pp) = [[(pp, False)]]
pc_normalise (PCUnion pc1 pc2) = (pc_normalise pc1) ++ (pc_normalise pc2)
pc_normalise (PCInter pc1 pc2) = combine (++) (pc_normalise pc1) (pc_normalise pc2)
pc_normalise (PCCompl pc) = case pc of
                        (PCPrim pp) -> [[(pp, True)]]
                        (PCUnion pc1 pc2) -> pc_normalise $ PCInter (PCCompl pc1) (PCCompl pc2)
                        (PCInter pc1 pc2) -> pc_normalise $ PCUnion (PCCompl pc1) (PCCompl pc2)
                        (PCCompl pc') ->  pc_normalise pc'

npc_simplify :: [[(PermPrim,Bool)]] -> [[(Int,Bool)]]
npc_simplify = mapMaybe inter_simplify
        where
                inter_simplify :: [(PermPrim,Bool)] -> Maybe [(Int,Bool)]
                inter_simplify [] = return []
                inter_simplify ((pp,b) : xs) = case pp of
                        PPFull -> if b then Nothing else inter_simplify xs
                        PPZero -> if b then inter_simplify xs else Nothing
                        (PPVar n) -> do
                                xs' <- inter_simplify xs
                                return $ (n,b) : xs'

correct_indexes :: Int -> [[(Int,Bool)]] -> [[(Int,Bool)]]
correct_indexes d = map (map ci)
        where
                ci (i,b) = (d - i - 1, b)

npc_empty :: (PermModel p) => p -> [[(Int,Bool)]] -> Bool
npc_empty et = (foldl (&&) True) . (map (isEmptyIntersection et))

pc_empty :: (PermModel p) => Int -> p -> PermComb -> Bool
pc_empty d et = (npc_empty et) . (correct_indexes d) . npc_simplify . pc_normalise

-- |Check a permission assertion using an Integer representation of binary trees.
permCheckBigInt :: PD.PermissionsProver
permCheckBigInt = return . Just . pf_eval . toPermSentence


