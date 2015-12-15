{-# LANGUAGE FlexibleContexts, MultiParamTypeClasses #-}
module Caper.Transitions where
import Prelude hiding (elem, foldr)
import Control.Monad
import Control.Monad.Reader.Class
import Control.Monad.IO.Class
import Data.Foldable

import Caper.ProverDatatypes
import Caper.Prover
import Caper.Utils.FloydWarshall
import Caper.RegionTypes
import Caper.Logger
-- import Caper.Provers -- TODO: remove (used for testing)

{-
data ClosureVariable v = Context v | Local String deriving (Eq, Ord)

instance (Show v) => Show (ClosureVariable v) where
        show (Context v) = "c_" ++ show v
        show (Local s) = "l_" ++ s

instance (StringVariable v) => StringVariable (ClosureVariable v) where
        varToString (Context v) = "c_" ++ varToString v
        varToString (Local s) = "l_" ++ s
-}

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
gtFreeVars gt = foldrFree (\v -> if v `elem` gtBoundVars gt then id else (v :)) [] (gtGuard gt)

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

-- |Given a 'GuardedTransition' and a pair of states, computes the condition
-- for that transition firing.  In particular, it checks if the condition
-- can never happen, or always happens.
computeCondition :: (MonadIO m, MonadReader r m, Provers r, Eq v, StringVariable v, MonadLogger m) =>
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

-- |Uses 'computeCondition' to determine how to instantiate the matrix.
-- Reflexive transitions are always allowed.
computeConditions :: (MonadIO m, MonadReader r m, Provers r, Eq v, StringVariable v, MonadLogger m) =>
        [GuardedTransition v] -> Int -> Int -> m (FOF ValueAtomic v)
computeConditions gts i j = if i == j then return FOFTrue else
                                foldM cc FOFFalse gts
                where
                        cc a b = do
                                b' <- computeCondition i j b
                                return (fmin a b')

translateIn :: Int -> (Int -> Int -> a) -> Int -> Int -> a
translateIn offset f x y = f (x + offset) (y + offset)

computeInitialMatrix :: (MonadIO m, MonadReader r m, Provers r, Eq v, StringVariable v, MonadLogger m) =>
        Int -> Int -> [GuardedTransition v] -> m (Matrix (FOF ValueAtomic v))
computeInitialMatrix lower upper gts = floydInitM (upper - lower + 1) (translateIn lower $ computeConditions gts)


-- This assumes the diagonal is true (which it will be if produced from a reflexive matrix).
matrixToReflRelation :: (Eq v) => Matrix (FOF ValueAtomic v) -> Integer -> ValueExpression v -> ValueExpression v -> FOF ValueAtomic v
matrixToReflRelation mx lower pre post = fmin (pre $=$ post) $ fst $ foldl' op1 (FOFFalse, lower) mx
                where
                        op1 (f, i) v = (fst $ foldl' (op2 i) (f, lower) v, i + 1)
                        op2 i (f, j) e | i == j = (f, j + 1)
                                       | otherwise = (fmin f (fadd e (FOFAnd (VEConst i $=$ pre) (VEConst j $=$ post))), j + 1)

-- |Compute an overapproximation of the closure of a set of transitions
--
-- TODO: rename this
computeClosureRelation :: (MonadIO m, MonadReader r m, Provers r, Eq v, StringVariable v, MonadLogger m) =>
        StateSpace -> [GuardedTransition v] -> m (ValueExpression v -> ValueExpression v -> FOF ValueAtomic v)
-- Best case scenario: no actions!
computeClosureRelation _ [] = return (\x y -> FOFAtom $ VAEq x y)
-- Finite state scenario
computeClosureRelation (StateSpace (Just lower) (Just upper)) gts = do
                        mx <- computeInitialMatrix lower upper gts
                        -- liftIO $ putStrLn $ show $ fmap (fmap (fmap varToString)) mx
                        let mx' = runFloyd mx
                        return $ matrixToReflRelation mx' (toInteger lower)
-- Fallback: universal relation
computeClosureRelation _ _ = return (\x y -> FOFTrue)


-- |Compute an underapproximation of the closure of a set of transitions
underComputeClosureRelation :: (MonadIO m, MonadReader r m, Provers r, Eq v, StringVariable v, MonadLogger m) =>
        StateSpace -> [GuardedTransition v] -> m (ValueExpression v -> ValueExpression v -> FOF ValueAtomic v)
-- No actions, so only identities
underComputeClosureRelation _ [] = return (\x y -> FOFAtom $ VAEq x y)
-- Finite state scenario
underComputeClosureRelation (StateSpace (Just lower) (Just upper)) gts = do
                        mx <- computeInitialMatrix lower upper gts
                        let mx' = runFloyd mx
                        return $ matrixToReflRelation mx' (toInteger lower)
-- Fallback: identity relation
underComputeClosureRelation _ _ = return (\x y -> FOFAtom $ VAEq x y)

{-
testgts = [ GuardedTransition [VIDNamed "x"]
        (FOFAnd (VEConst 7 $<$ (VEVar $ VIDNamed "a"))
                (VEVar (VIDNamed "x") $=$ VEConst 1))
        (VEVar $ VIDNamed "x")
        (VEConst 1 $-$ VEVar (VIDNamed "x")) ]
-}