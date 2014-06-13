{-# LANGUAGE FlexibleContexts #-}
module Transitions where
import Control.Monad
import Control.Monad.Reader.Class
import Control.Monad.IO.Class
import ProverDatatypes
import Prover
import FloydWarshall
import Prelude hiding (foldl', elem, foldr)
import Data.Foldable

import Provers -- TODO: remove (used for testing)

data ClosureVariable v = Context v | Local String deriving (Eq, Ord)

instance (Show v) => Show (ClosureVariable v) where
        show (Context v) = "c_" ++ (show v)
        show (Local s) = "l_" ++ s

instance (StringVariable v) => StringVariable (ClosureVariable v) where
        varToString (Context v) = "c_" ++ (varToString v)
        varToString (Local s) = "l_" ++ s

-- ssLowerBound and ssUpperBound are the (inclusive) lower
-- and upper bounds of the state space.
-- invariant: ssLowerBound <= ssUpperBound (if both are not Nothing)
data StateSpace = StateSpace {
                ssLowerBound :: Maybe Int,
                ssUpperBound :: Maybe Int
                }
isFinite :: StateSpace -> Bool
isFinite (StateSpace (Just _) (Just _)) = True
isFinite _ = False

ssSize :: (MonadPlus m) => StateSpace -> m Int
ssSize (StateSpace (Just x) (Just y)) = return $ y - x + 1
ssSize _ = mzero

{- OK.
 - I want to compute a formula that represents the transitive closure of
 - a set of transitions, assuming a finite state space.  Roughly the algorithm
 - will work as follows:
 - 1. Initialise a one-step reachability matrix; the i,j-th entry is a
 -    predicate that is true when there is a transition from i to j according
 -    to any of the transitions.
 - 2. Compute the transitive reachability matrix using Floyd-Warshall; the
 -    i,j-th entry will then be a predicate that is true if there is a series
 -    of transitions going from i to j.
 - 3. Convert this matrix to a formula.
 -
 - Input:
 -   upper and lower bounds on the state space
 -   a list of guarded transitions, each consisting of:
 -     a list of variable bindings
 -     a FOF predicate describing when the transition can apply (may contain
 -       both bound and free variables)
 -     an expression describing the initial state for the transition (bv only)
 -     an expression describing the final state for the transition (bv only)
 -}

data GuardedTransition vt = GuardedTransition {
        gtBoundVars :: [vt],
        gtGuard :: FOF ValueAtomic vt,
        gtPreState :: ValueExpression vt,
        gtPostState :: ValueExpression vt
        }
gtFreeVars :: Eq vt => GuardedTransition vt -> [vt]
gtFreeVars gt = foldrFree (\v -> if elem v (gtBoundVars gt) then id else (v :)) [] (gtGuard gt)

instance (Show vt) => Show (GuardedTransition vt) where
        show (GuardedTransition bvs gd pre post) = 
                show bvs ++ ": " ++ show gd ++ " | " ++ show pre ++ " ~> " ++ show post

instance (Eq b, Eq (a b)) => Floydable (FOF a b) where
        -- fmin is a slightly simplifying version of FOFOr
        fmin FOFTrue _ = FOFTrue
        fmin _ FOFTrue = FOFTrue
        fmin FOFFalse x = x
        fmin x FOFFalse = x
        fmin x y | x == y = x
                 | otherwise = FOFOr x y
        -- fadd is a slightly simplifying FOFAnd
        fadd FOFFalse _ = FOFFalse
        fadd _ FOFFalse = FOFFalse
        fadd FOFTrue x = x
        fadd x FOFTrue = x
        fadd x y | x == y = x
                 | otherwise = FOFAnd x y
        -- finfty is FOFFalse
        finfty = FOFFalse

-- Given a GuardedTransition and a pair of states, computes the condition
-- for that transition firing.  In particular, it checks if the condition
-- can never happen, or always happens.
computeCondition :: (MonadIO m, MonadReader r m, Provers r, Eq v, StringVariable v) =>
        Int -> Int -> GuardedTransition v -> m (FOF ValueAtomic v)
computeCondition i j t = do
        let cond = foldr FOFExists (FOFAnd (gtGuard t) (FOFAnd (gtPreState t $=$ VEConst (toInteger i)) (gtPostState t $=$ VEConst (toInteger j)))) (gtBoundVars t)
        never <- valueCheck (foldr FOFExists cond (gtFreeVars t))
        case never of
                Just False -> return FOFFalse
                _ -> do 
                        always <- valueCheck (foldr FOFForAll cond (gtFreeVars t))
                        case always of
                                Just True -> return FOFTrue
                                _ -> return cond

computeConditions :: (MonadIO m, MonadReader r m, Provers r, Eq v, StringVariable v) =>
        [GuardedTransition v] -> Int -> Int -> m (FOF ValueAtomic v)
computeConditions gts i j = if i == j then return FOFTrue else
                                foldM cc FOFFalse gts
                where
                        cc a b = do
                                b' <- computeCondition i j b
                                return (fmin a b')

-- This assumes the diagonal is true.
matrixToReflRelation :: (Eq v) => Matrix (FOF ValueAtomic v) -> Integer -> ValueExpression v -> ValueExpression v -> FOF ValueAtomic v
matrixToReflRelation mx lower pre post = fmin (pre $=$ post) $ fst $ foldl' op1 (FOFFalse, lower) mx
                where
                        op1 (f, i) v = (fst $ foldl' (op2 i) (f, lower) v, i + 1)
                        op2 i (f, j) e | i == j = (f, j + 1)
                                       | otherwise = (fmin f (fadd e (FOFAnd (VEConst i $=$ pre) (VEConst j $=$ post))), j + 1)


testgts = [ GuardedTransition [VIDNamed "x"] (FOFAnd ((VEConst 7) $<$ (VEVar $ VIDNamed "a")) ((VEVar $ VIDNamed "x") $=$ (VEConst 1))) (VEVar $ VIDNamed "x") ((VEConst 1) $-$ (VEVar $ VIDNamed "x")) ]
