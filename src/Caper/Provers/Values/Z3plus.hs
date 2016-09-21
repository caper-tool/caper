-- |This module provides an implementation of entailment checking for value
-- formulae using the Z3 theorem prover (via FFI) and making use of incremental
-- proving.  The incremental prover progressively builds a context of
-- assumptions (which may be pushed and popped) and so can reuse information
-- between calls.  It is often significantly faster than the one-shot prover.
-- However, it is less complete.  In particular, it doesn't handle
-- quantification (or at least not much).  To handle this, we fall back to
-- one-shot mode when the assertions contain quantifiers, or when invoking Z3
-- results in "UNKNOWN (incomplete quantifiers)".
--
-- Note that this was developed against Z3 version 4.4.1.  Future changes to Z3
-- may require updating this module.
module Caper.Provers.Values.Z3plus(
    valueProverInfo,
    createEntailsChecker
    ) where

import Control.Monad
import Z3.Monad
import Control.Concurrent.MVar
import Data.List hiding (foldr)
import Control.Exception hiding (assert)

import Caper.ProverDatatypes

-- |A context of assumptions.  This is a list of lists of formulae, since we
-- push and pop a list of assumptions at a time.
type Assms = [[FOF ValueAtomic VariableID]]

-- |An assumption environment is a Z3 environment together with a context of
-- assumptions that correspond to the stack of assertions of the Z3
-- environment.
data AssumptionEnvironment = AssumptionEnvironment Z3Env Assms

-- |Create an assumption environment with an empty stack of assumptions and
-- with the given tiemout.
makeEmptyAssumptionEnvironment ::
    Maybe Int                       -- ^Optional timeout in milliseconds
    -> IO AssumptionEnvironment
makeEmptyAssumptionEnvironment timeout = do
        env <- newEnv (Just AUFLIA) stdOpts
        flip evalZ3WithEnv env $ do
                params <- mkParams
                tmo <- mkStringSymbol "timeout"
                paramsSetUInt params tmo (case timeout of
                        Just x -> if x > 0 then toEnum x else 0
                        Nothing -> 0)
                solverSetParams params
        return $ AssumptionEnvironment env []

-- |Convert a 'VariableID' to a Z3 AST representation.
getAssmVar :: (MonadZ3 z3) => VariableID -> z3 AST
getAssmVar v = do
        s <- mkStringSymbol $ varToString v
        mkIntVar s

-- |Convert a 'ValueExpression' to a Z3 AST representation.
convExpression :: (MonadZ3 z3) =>
    (v -> z3 AST)           -- ^Variable representation
    -> ValueExpression v    -- ^Expression to convert
    -> z3 AST
convExpression s (VEConst i) = mkInteger i
convExpression s (VEVar v) = s v
convExpression s (VEPlus e1 e2) = do
                c1 <- convExpression s e1
                c2 <- convExpression s e2
                mkAdd [c1, c2]
convExpression s (VEMinus e1 e2) = do
                c1 <- convExpression s e1
                c2 <- convExpression s e2
                mkSub [c1, c2]
convExpression s (VETimes e1 e2) = do
                c1 <- convExpression s e1
                c2 <- convExpression s e2
                mkMul [c1, c2]

-- |Convert a 'ValueAtomic' to a Z3 AST representation
convAtomic :: (MonadZ3 z3) =>
    (v -> z3 AST)           -- ^Variable representation
    -> ValueAtomic v        -- ^Atomic proposition to convert
    -> z3 AST
convAtomic s (VAEq e1 e2) = do
                c1 <- convExpression s e1
                c2 <- convExpression s e2
                mkEq c1 c2
convAtomic s (VALt e1 e2) = do
                c1 <- convExpression s e1
                c2 <- convExpression s e2
                mkLt c1 c2

-- |Convert a first-order value formula to a Z3 AST representation.
convFOF :: (MonadZ3 z3) =>
    (VariableID -> Maybe Int)       -- ^DeBrujin indices for bound variables
    -> FOF ValueAtomic VariableID   -- ^Formula to convert
    -> z3 AST
convFOF bdgs (FOFForAll v f) = do
                si <- mkStringSymbol ("EE" ++ varToString v)
                x <- convFOF (\w -> if w == v then Just 0 else (1+) <$> bdgs w) f
                intS <- mkIntSort
                mkForall [] [si] [intS] x
convFOF bdgs (FOFExists v f) = do
                si <- mkStringSymbol ("EE" ++ varToString v)
                x <- convFOF (\w -> if w == v then Just 0 else (1+) <$> bdgs w) f
                intS <- mkIntSort
                mkExists [] [si] [intS] x
convFOF bdgs (FOFAtom a) = convAtomic bdgs' a
        where
                bdgs' v = case bdgs v of
                        Nothing -> getAssmVar v
                        Just n -> mkBound n =<< mkIntSort
convFOF bdgs (FOFAnd f1 f2) = mkAnd =<< sequence (convFOF bdgs <$> [f1, f2])
convFOF bdgs (FOFOr f1 f2) = mkOr =<< sequence (convFOF bdgs <$> [f1, f2])
convFOF bdgs (FOFImpl f1 f2) = do
                c1 <- convFOF bdgs f1
                c2 <- convFOF bdgs f2
                mkImplies c1 c2
convFOF bdgs (FOFNot f1) = mkNot =<< convFOF bdgs f1
convFOF bdgs FOFFalse = mkFalse
convFOF bdgs FOFTrue = mkTrue

-- |Determine if a first-order formula has quantifiers apart from a prefix of
-- existentials.
nontrivialQuantifiers :: FOF a v -> Bool
nontrivialQuantifiers (FOFExists _ f) = nontrivialQuantifiers f
nontrivialQuantifiers f0 = anyQuantifiers f0
    where
        anyQuantifiers (FOFExists _ _) = True
        anyQuantifiers (FOFForAll _ _) = True
        anyQuantifiers (FOFAnd f1 f2) = anyQuantifiers f1 || anyQuantifiers f2
        anyQuantifiers (FOFOr f1 f2) = anyQuantifiers f1 || anyQuantifiers f2
        anyQuantifiers (FOFImpl f1 f2) = anyQuantifiers f1 || anyQuantifiers f2
        anyQuantifiers (FOFNot f) = anyQuantifiers f
        anyQuantifiers _ = False
        

-- |Given a context of assumptions representing the current Z3 environment,
-- update the environment and context to match the list of assumptions given.
updateAssumptions :: (MonadZ3 z3) =>
    Assms                               -- ^Current assumption context
    -> [FOF ValueAtomic VariableID]     -- ^Required assumptions
    -> z3 Assms
updateAssumptions [] [] = return []
updateAssumptions [] ams = do
                        push
                        sequence_ $ (assert <=< convFOF (const Nothing)) <$> ams
                        return [ams]
updateAssumptions (ams1 : ar) ams = case stripPrefix ams1 ams of
        Nothing -> do
                pop (1 + length ar)
                updateAssumptions [] ams
        Just ams' -> (ams1 :) <$> updateAssumptions ar ams'

-- |Check if assumptions entail an assertion.  This uses Z3's one-shot solver.
-- This is more complete, but slower than the incremental solver, so we use it
-- as a fallback when we can't depend on the incremental solver.
fallbackCheck :: Maybe Int -> [FOF ValueAtomic VariableID] -> FOF ValueAtomic VariableID -> IO (Maybe Bool)
fallbackCheck timeout ams ast = evalZ3With Nothing stdOpts $ do
                params <- mkParams
                tmo <- mkStringSymbol "timeout"
                paramsSetUInt params tmo (case timeout of
                        Just x -> if x > 0 then toEnum x else 0
                        Nothing -> 0)
                solverSetParams params
                let stmt0 = foldr FOFAnd (FOFNot ast) ams
                let stmt1 = foldr FOFExists stmt0 (freeVariables stmt0)
                assert =<< convFOF (const Nothing) stmt1
                res <- check
                return $ case res of
                        Sat -> Just False
                        Unsat -> Just True
                        _ -> Nothing


-- |Check if assumptions entail an assertion.  This uses the incremental
-- checker but will fall back to the one-shot checker if:
--
--  1. The assertion contains quantifiers other than a prefix of
--     existentials.
--  2. The solver returns unknown with the reason "(incomplete quantifiers)".
--
-- In both cases, it is more likely that the one-shot solver will do a better
-- job.
entailsCheck :: Maybe Int               -- ^Optional timeout in milliseconds
    -> MVar AssumptionEnvironment       -- ^Shared assumption environment
    -> [FOF ValueAtomic VariableID]     -- ^Assumptions
    -> FOF ValueAtomic VariableID       -- ^Assertion
    -> IO (Maybe Bool)
entailsCheck timeout mvAE ams ast
    | nontrivialQuantifiers ast = fallbackCheck timeout ams ast
    | otherwise = do
                oae <- tryTakeMVar mvAE
                (AssumptionEnvironment env assms) <- case oae of
                        Just ae -> return ae
                        Nothing -> (makeEmptyAssumptionEnvironment timeout)
                (assms', res, rtry) <- flip evalZ3WithEnv env $ do
                        assms' <- updateAssumptions assms (reverse ams)
                        (res, rtry) <- local $ do
                                assert =<< convFOF (const Nothing) (FOFNot ast)
                                res <- check
                                rtry <- if (res == Undef) then do
                                            -- s2s <- solverToString
                                            reason <- solverGetReasonUnknown
                                            -- liftIO $ appendFile "z3plus.log" $ s2s ++ "\n" ++ "UNKNOWN: " ++ reason ++ "\n"
                                            -- liftIO $ putStrLn $ "UNKNOWN: " ++ reason
                                            return (reason == "(incomplete quantifiers)")
                                        else return False
                                return (res, rtry)
                        return (assms', res, rtry)
                _ <- tryPutMVar mvAE (AssumptionEnvironment env assms')
                case res of
                        Sat -> return $ Just False
                        Unsat -> return $ Just True
                        _ -> if rtry then fallbackCheck timeout ams ast else return Nothing

-- |Initialise an incremental checker.
createEntailsChecker :: Maybe Int -- ^Optional timeout in milliseconds
    -> IO ([FOF ValueAtomic VariableID] -> FOF ValueAtomic VariableID -> IO (Maybe Bool))
createEntailsChecker timeout = do
                mvAE <- newEmptyMVar
                return (entailsCheck timeout mvAE)

-- |Obtain a string describing the value checker provided by this module.
valueProverInfo :: IO String
valueProverInfo = (do
        ver <- evalZ3 getVersion
        return $ "Z3 library, version " ++ show ver ++ " (reusing contexts)") `catch`
        (\e -> return $ "Failed to invoke Z3:\n" ++ show (e :: SomeException))
