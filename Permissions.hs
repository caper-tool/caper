
module Permissions (DPF(..), dImpl, dEmp, dpf_eval) where
import Data.List

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

test1 = DEx (DAll (DDis 0 1))
test2 = DEx (DAll (dImpl (DAll (DDis 0 1)) (DEq 0 1)))
test2a = DEx (DAll (DEx (dImpl (DDis 0 1) (DEq 1 2))))
test3 = DEx (DAnd (DAll (DDis 0 1)) (DAll (dImpl (DAll (DDis 0 1)) (DEq 0 1))))
test3a = DEx (DAll (DAll (DEx (DAnd (DDis 2 3) (DOr (DNot (DDis 1 0)) (DEq 1 3))))))
test4 = DAll $ dImpl (DAll (DOr (dEmp 0) (DNot (DDis 0 1)))) (DAll $ DAll $ DAll $ DAll $ dImpl (DC 0 1 4) (dImpl (DC 2 3 4) (dImpl (DEq 0 2) (DEq 1 3))))
test5 = DAll $ DOr (DDis 0 0) (DEx $ DEx $ DAnd (DAnd (DNot (DDis 0 0)) (DNot (DDis 1 1))) (DC 0 1 2))


trees 0 = [ETSome]
trees n = foldl (++) [] $ map et_splits (trees (n-1))

trees2 = foldl (++) [] $ map et_splits $ et_splits ETSome


testTrees [] = return ()
testTrees (x:xs) = do
        putStrLn (show x)
        putStrLn $ "  " ++ (show (eval_empty_inters x [(0,True),(2,False)]))
        testTrees xs
        
