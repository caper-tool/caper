
module Permissions (permCheckTree) where
import Data.List
import Data.Maybe
import Control.Parallel.Strategies
import qualified ProverDatatypes as PD


data DPF = DFalse | DAnd DPF DPF | DOr DPF DPF | DNot DPF | DEq Int Int | DC Int Int Int
        | DAll DPF | DEx DPF | DDis Int Int | DZero Int | DFull Int
        | DTotalFull [Int] deriving (Show)

dImpl a b = DOr (DNot a) b
dEmp a = DDis a a

data EvalTree = ETSome | ETNone | ETBranch EvalTree EvalTree

instance Show EvalTree where
        show ETSome = "@"
        show ETNone = "."
        show (ETBranch t1 t2) = "(" ++ show t1 ++ " " ++ show t2 ++ ")"
        

dpf_eval :: DPF -> Bool
dpf_eval = dpf_eval_env 0 ETSome

dpf_eval_env :: Int -> EvalTree -> DPF -> Bool
dpf_eval_env _ _ DFalse = False
dpf_eval_env d et (DAnd f1 f2) = dpf_eval_env d et f1 && dpf_eval_env d et f2
dpf_eval_env d et (DOr f1 f2) = dpf_eval_env d et f1 || dpf_eval_env d et f2
dpf_eval_env d et (DNot f) = not $ dpf_eval_env d et f
dpf_eval_env d et (DAll f) = foldl (&&) True (map (\e -> dpf_eval_env (d+1) e f) (et_splits et))
dpf_eval_env d et (DEx f) = foldl (||) False (map (\e -> dpf_eval_env (d+1) e f) (et_splits et))
dpf_eval_env d et (DEq n m) = eval_eq et (d - n - 1) (d - m - 1)
dpf_eval_env d et (DDis n m) = eval_empty_inters et [(d - n - 1,False),(d - m - 1,False)]
dpf_eval_env d et (DC n m nm) = eval_empty_inters et [(d - n - 1,False),(d - m - 1,False)] &&
				eval_empty_inters et [(d - n - 1,True),(d - m - 1,True),(d - nm - 1,False)] &&
				eval_empty_inters et [(d - n - 1,False),(d - nm - 1,True)] &&
				eval_empty_inters et [(d - m - 1,False),(d - nm - 1,True)]
dpf_eval_env d et (DZero n) = eval_empty_inters et [(d - n - 1,False)]
dpf_eval_env d et (DFull n) = eval_empty_inters et [(d - n - 1,True)]
dpf_eval_env d et (DTotalFull ns) = eval_empty_inters et (map (\n -> (d - n - 1, True)) ns)


eval_eq :: EvalTree -> Int -> Int -> Bool
eval_eq _ 0 0 = True
eval_eq ETNone _ _ = True
eval_eq ETSome 0 _ = error "Tree does not evaluate all variables"
eval_eq (ETBranch t1 t2) 0 m = match_positive t1 (m-1) && match_negative t2 (m-1)
eval_eq et m 0 = eval_eq et 0 m
eval_eq (ETBranch t1 t2) n m = if n <= 0 || m <= 0 then error "Bad variable index" else eval_eq t1 (n-1) (m-1) && eval_eq t2 (n-1) (m-1)

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


eval_empty :: EvalTree -> Int -> Bool
eval_empty ETNone _ = True
eval_empty ETSome _ = False
eval_empty (ETBranch t1 t2) 0 = False
eval_empty (ETBranch t1 t2) n = eval_empty t1 (n-1) && eval_empty t2 (n-1)

match_positive :: EvalTree -> Int -> Bool
match_positive ETSome _ = error "match_positive: Tree does not evaluate all variables"
match_positive ETNone _ = True
match_positive (ETBranch _ ETNone) 0 = True
match_positive (ETBranch _ _) 0 = False
match_positive (ETBranch t1 t2) n = if n <= 0 then error "match_positive: Bad variable index" else match_positive t1 (n-1) && match_positive t2 (n-1)

match_negative :: EvalTree -> Int -> Bool
match_negative ETSome _ = error "match_negative: Tree does not evaluate all variables"
match_negative ETNone _ = True
match_negative (ETBranch ETNone _) 0 = True
match_negative (ETBranch _ _) 0 = False
match_negative (ETBranch t1 t2) n = if n <= 0 then error "match_negative: Bad variable index" else match_negative t1 (n-1) && match_negative t2 (n-1)


combine :: (a -> b -> c) -> [a] -> [b] -> [c]
combine f [] l2 = []
combine f (x : xs) l2 = map (f x) l2 ++ combine f xs l2

et_splits :: EvalTree -> [EvalTree]
et_splits ETSome = [ETBranch ETSome ETSome, ETBranch ETSome ETNone, ETBranch ETNone ETSome]
et_splits ETNone = [ETNone]
et_splits (ETBranch et1 et2) = combine ETBranch (et_splits et1) (et_splits et2)


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



testpf1 = PFAll $ PFImpl (PFEx $ PFEx $ PFAnd (PFAtom $ PAEqual (PESum (PEVar 0) (PEVar 1)) (PEVar 2)) (PFAtom $ PAEqual (PEVar 0) (PEVar 1))) (PFAtom $ PADisjoint (PEVar 0) PEFull)

pf_eval :: PermFormula -> Bool
pf_eval = pf_eval_env 0 ETSome

pf_eval_env :: Int -> EvalTree -> PermFormula -> Bool
pf_eval_env _ _ PFFalse = False
pf_eval_env _ _ PFTrue = True
pf_eval_env d et (PFNot f) = not $ pf_eval_env d et f
pf_eval_env d et (PFAnd f1 f2) = pf_eval_env d et f1 && pf_eval_env d et f2
pf_eval_env d et (PFOr f1 f2) = pf_eval_env d et f1 || pf_eval_env d et f2
pf_eval_env d et (PFImpl f1 f2) = if pf_eval_env d et f1 then pf_eval_env d et f2 else True
pf_eval_env d et (PFAll f) = foldl (&&) True (parMap rseq (\e -> pf_eval_env (d+1) e f) (et_splits et))
pf_eval_env d et (PFEx f) = foldl (||) False (parMap rseq (\e -> pf_eval_env (d+1) e f) (et_splits et))
pf_eval_env d et (PFAtom a) = pa_eval_env d et a

pa_eval_env :: Int -> EvalTree -> PermAtom -> Bool
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

npc_empty :: EvalTree -> [[(Int,Bool)]] -> Bool
npc_empty et = (foldl (&&) True) . (map (eval_empty_inters et))

pc_empty :: Int -> EvalTree -> PermComb -> Bool
pc_empty d et = (npc_empty et) . (correct_indexes d) . npc_simplify . pc_normalise

permCheckTree :: PD.PermissionsProver
-- ^Check a permission assertion using a tree-based representation.
permCheckTree = return . Just . pf_eval . toPermSentence





dpf_to_pf :: DPF -> PermFormula
dpf_to_pf DFalse = PFFalse
dpf_to_pf (DAnd dpf1 dpf2) = PFAnd (dpf_to_pf dpf1) (dpf_to_pf dpf2)
dpf_to_pf (DOr dpf1 dpf2) = PFOr (dpf_to_pf dpf1) (dpf_to_pf dpf2)
dpf_to_pf (DNot dpf1) = PFNot (dpf_to_pf dpf1)
dpf_to_pf (DEq n1 n2) = PFAtom $ PAEqual (PEVar n1) (PEVar n2)
dpf_to_pf (DC n1 n2 n3) = PFAtom $ PAEqual (PESum (PEVar n1) (PEVar n2)) (PEVar n3)
dpf_to_pf (DAll dpf) = PFAll $ dpf_to_pf dpf
dpf_to_pf (DEx dpf) = PFEx $ dpf_to_pf dpf
dpf_to_pf (DDis n1 n2) = PFAtom $ PADisjoint (PEVar n1) (PEVar n2)
dpf_to_pf (DZero n) = PFAtom $ PAEqual (PEVar n) PEZero
dpf_to_pf (DFull n) = PFAtom $ PAEqual (PEVar n) PEFull
dpf_to_pf _ = error "!"





test1 = DEx (DAll (DDis 0 1))
test2 = DEx (DAll (dImpl (DAll (DDis 0 1)) (DEq 0 1)))
test2a = DEx (DAll (DEx (dImpl (DDis 0 1) (DEq 1 2))))
test3 = DEx (DAnd (DAll (DDis 0 1)) (DAll (dImpl (DAll (DDis 0 1)) (DEq 0 1))))
test3a = DEx (DAll (DAll (DEx (DAnd (DDis 2 3) (DOr (DNot (DDis 1 0)) (DEq 1 3))))))
test4 = DAll $ dImpl (DAll (DOr (dEmp 0) (DNot (DDis 0 1)))) (DAll $ DAll $ DAll $ DAll $ dImpl (DC 0 1 4) (dImpl (DC 2 3 4) (dImpl (DEq 0 2) (DEq 1 3))))
test5 = DAll $ DOr (DDis 0 0) (DEx $ DEx $ DAnd (DAnd (DNot (DDis 0 0)) (DNot (DDis 1 1))) (DC 0 1 2))

testCrossSplit = PFAll $ PFAll $ PFAll $ PFAll $ PFImpl
        (PFAtom $ PAEqual (PESum (PEVar 0) (PEVar 1)) (PESum (PEVar 2) (PEVar 3))) $
        PFEx $ PFEx $ PFEx $ PFEx $
        (PFAnd (PFAnd (PFAtom $ PAEqual (PESum (PEVar 0) (PEVar 1)) (PEVar 4))
                        (PFAtom $ PAEqual (PESum (PEVar 2) (PEVar 3)) (PEVar 5)))
                (PFAnd (PFAtom $ PAEqual (PESum (PEVar 0) (PEVar 2)) (PEVar 6))
                        (PFAtom $ PAEqual (PESum (PEVar 1) (PEVar 3)) (PEVar 7))))


trees 0 = [ETSome]
trees n = foldl (++) [] $ map et_splits (trees (n-1))

trees2 = foldl (++) [] $ map et_splits $ et_splits ETSome


testTrees [] = return ()
testTrees (x:xs) = do
        putStrLn (show x)
        putStrLn $ "  " ++ (show (eval_empty_inters x [(0,True),(2,False)]))
        testTrees xs

foo :: IO ()
foo = print $ pf_eval $ dpf_to_pf $ DEx test4
