module Caper.Provers.Values.Z3plus where

import Control.Monad
import Control.Monad.IO.Class
import Z3.Monad
import Control.Concurrent.MVar
import Data.List
import Control.Exception hiding (assert)

import Caper.ProverDatatypes

type Assms = [[FOF ValueAtomic VariableID]]

data AssumptionEnvironment = AssumptionEnvironment {
        aeEnv :: Z3Env,
        aeAssms :: Assms
        }

makeEmptyAssumptionEnvironment :: Maybe Int -> IO AssumptionEnvironment
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

getAssmVar :: (MonadZ3 z3) => VariableID -> z3 AST
getAssmVar v = do
        s <- mkStringSymbol $ varToString v
        mkIntVar s


convExpression :: (MonadZ3 z3) => (v -> z3 AST) -> ValueExpression v -> z3 AST
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

convAtomic :: (MonadZ3 z3) => (v -> z3 AST) -> ValueAtomic v -> z3 AST
convAtomic s (VAEq e1 e2) = do
                c1 <- convExpression s e1
                c2 <- convExpression s e2
                mkEq c1 c2
convAtomic s (VALt e1 e2) = do
                c1 <- convExpression s e1
                c2 <- convExpression s e2
                mkLt c1 c2


convFOF :: (MonadZ3 z3) => (VariableID -> Maybe Int) -> FOF ValueAtomic VariableID -> z3 AST
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


updateAssumptions :: (MonadZ3 z3) => Assms -> [FOF ValueAtomic VariableID] -> z3 Assms
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


entailsCheck :: IO AssumptionEnvironment -> MVar AssumptionEnvironment -> 
        [FOF ValueAtomic VariableID] -> FOF ValueAtomic VariableID -> IO (Maybe Bool)
entailsCheck defAE mvAE ams ast = do
                oae <- tryTakeMVar mvAE
                (AssumptionEnvironment env assms) <- case oae of
                        Just ae -> return ae
                        Nothing -> defAE
                (assms', res) <- flip evalZ3WithEnv env $ do
                        assms' <- updateAssumptions assms (reverse ams)
                        res <- local $ do
                                assert =<< convFOF (const Nothing) (FOFNot ast)
                                res <- check
                                s2s <- solverToString
                                liftIO $ putStrLn s2s
                                when (res == Undef) $ do
                                    reason <- solverGetReasonUnknown
                                    liftIO $ putStrLn $ "UNKNOWN: " ++ reason
                                return res
                        return (assms', res)
                _ <- tryPutMVar mvAE (AssumptionEnvironment env assms')
                return $ case res of
                        Sat -> Just False
                        Unsat -> Just True
                        _ -> Nothing

createEntailsChecker :: Maybe Int -> IO ([FOF ValueAtomic VariableID] -> FOF ValueAtomic VariableID -> IO (Maybe Bool))
createEntailsChecker timeout = do
                mvAE <- newEmptyMVar
                return (entailsCheck (makeEmptyAssumptionEnvironment timeout) mvAE)

valueProverInfo :: IO String
valueProverInfo = (do
        ver <- evalZ3 getVersion
        return $ "Z3 library, version " ++ show ver ++ " (reusing contexts)") `catch`
        (\e -> return $ "Failed to invoke Z3:\n" ++ show (e :: SomeException))
