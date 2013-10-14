{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Interpreter where

import AST
import Parser
import Environment
import Control.Monad.State
import Data.IORef
import System.IO
import Text.ParserCombinators.Parsec

class Eval a b where
  eval :: Env -> a -> IOThrowsError b

instance Eval BExpr Bool where
  eval env (ConstBExpr _ b)                      = return b
  eval env (NotBExpr _ e)                        = (eval env e) >>= return . not
  eval env (BinaryBExpr _ And e1 e2)             = do r1 <- (eval env e1)
                                                      r2 <- (eval env e2)
                                                      return $ r1 && r2
  eval env (BinaryBExpr _ Or e1 e2)              = do r1 <- (eval env e1)
                                                      r2 <- (eval env e2)
                                                      return $ r1 || r2
  eval env (RBinaryBExpr _ Equal e1 e2)          = do r1 <- ((eval :: Env -> AExpr -> IOThrowsError Integer) env e1)
                                                      r2 <- ((eval :: Env -> AExpr -> IOThrowsError Integer) env e2)
                                                      return $ r1 == r2
  eval env (RBinaryBExpr _ NotEqual e1 e2)       = do r1 <- ((eval :: Env -> AExpr -> IOThrowsError Integer) env e1)
                                                      r2 <- ((eval :: Env -> AExpr -> IOThrowsError Integer) env e2)
                                                      return $ r1 /= r2
  eval env (RBinaryBExpr _ Greater e1 e2)        = do r1 <- ((eval :: Env -> AExpr -> IOThrowsError Integer) env e1)
                                                      r2 <- ((eval :: Env -> AExpr -> IOThrowsError Integer) env e2)
                                                      return $ r1 > r2
  eval env (RBinaryBExpr _ GreaterOrEqual e1 e2) = do r1 <- ((eval :: Env -> AExpr -> IOThrowsError Integer) env e1)
                                                      r2 <- ((eval :: Env -> AExpr -> IOThrowsError Integer) env e2)
                                                      return $ r1 >= r2
  eval env (RBinaryBExpr _ Less e1 e2)           = do r1 <- ((eval :: Env -> AExpr -> IOThrowsError Integer) env e1)
                                                      r2 <- ((eval :: Env -> AExpr -> IOThrowsError Integer) env e2)
                                                      return $ r1 < r2
  eval env (RBinaryBExpr _ LessOrEqual e1 e2)    = do r1 <- ((eval :: Env -> AExpr -> IOThrowsError Integer) env e1)
                                                      r2 <- ((eval :: Env -> AExpr -> IOThrowsError Integer) env e2)
                                                      return $ r1 >= r2

instance Eval AExpr Integer where
  eval env (VarAExpr _  n)                = return 0
  eval _ (ConstAExpr _ i)                 = return i
  eval env (NegAExpr _ e)                 = (eval env e) >>= return . negate
  eval env (BinaryAExpr _ Add e1 e2)      = do r1 <- (eval env e1)
                                               r2 <- (eval env e2)
                                               return $ r1 + r2
  eval env (BinaryAExpr _ Subtract e1 e2) = do r1 <- (eval env e1)
                                               r2 <- (eval env e2)
                                               return $ r1 - r2
  eval env (BinaryAExpr _ Multiply e1 e2) = do r1 <- (eval env e1)
                                               r2 <- (eval env e2)
                                               return $ r1 * r2
  eval env (BinaryAExpr _ Divide e1 e2)   = do r1 <- (eval env e1)
                                               r2 <- (eval env e2)
                                               return $ quot r1 r2

instance Eval Stmt () where
  eval env (SeqStmt _ seq)         = mapM ((eval :: Env -> Stmt -> IOThrowsError ()) env) seq >> return ()
  eval env (VarStmt _ vars)        = mapM (varStore env) vars >> return ()
--  eval env (LocalAssignStmt _ n e) = n ++ " := " ++ show e ++ ";"
--  eval env (DerefStmt _ n e)       = n ++ " := [" ++ show e ++ "];"  
  eval env (AssignStmt _ e1 e2)    = do r1 <- (eval env e1)
                                        r2 <- (eval env e2)
                                        writeHeap env r1 r2
                                        return ()
  eval env (IfElseStmt _ b s1 s2)  = do c <- (eval env b)
                                        if c
                                          then (eval env s1) >>= return
                                          else (eval env s2) >>= return
  eval env (WhileStmt _ _ e s)     = return ()
  eval env (DoWhileStmt _ _ s e)   = return ()
  eval env (ReturnStmt _ Nothing)  = return ()
  eval env (ReturnStmt _ (Just e)) = return ()
  eval env (SkipStmt _)            = return ()

--eval :: Env -> Integer -> IOThrowsError Integer
--eval env var = allocHeap env var

evalAndPrint :: Env -> String -> IO ()
evalAndPrint env expr =  evalString env expr >>= putStrLn

evalString :: Env -> String -> IO String
evalString env expr = runIOThrows $ liftM show $ (liftThrows $ parseStatement expr) >>= (eval :: Env -> Stmt -> IOThrowsError ()) env

until_ :: Monad m => (a -> Bool) -> m a -> (a -> m ()) -> m ()
until_ pred prompt action = do 
  result <- prompt
  if pred result then return () else action result >> until_ pred prompt action

flushStr :: String -> IO ()
flushStr str = putStr str >> hFlush stdout

readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine

runInterpreter :: IO ()
runInterpreter = emptyEnv >>= until_ (== "quit") (readPrompt "> ") . evalAndPrint
