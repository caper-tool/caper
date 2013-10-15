{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}

module Interpreter where

import AST
import Parser
import Environment
import Data.IORef
import Data.List
import Data.Typeable
import Control.Monad.State
import Control.Exception;
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
  eval env (VarAExpr _  n)                = readStore env n
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

instance Eval Stmt (Maybe Integer) where
  eval env (VarStmt _ vars)               = mapM (varStore env) vars >> return Nothing
  eval env (SeqStmt _ [])                 = return Nothing
  eval env (SeqStmt p (x:xs))             = do r <- (eval :: Env -> Stmt -> IOThrowsError (Maybe Integer)) env x
                                               case r of
                                                 Just v  -> return $ Just v
                                                 Nothing -> (eval :: Env -> Stmt -> IOThrowsError (Maybe Integer)) env (SeqStmt p xs)
  eval env (IfElseStmt _ b s1 s2)         = do r <- (eval env b)
                                               if r
                                                 then (eval env s1)
                                                 else (eval env s2)
  eval env w@(WhileStmt _ _ e s)          = do r <- (eval :: Env -> BExpr -> IOThrowsError Bool) env e
                                               if r
                                                 then do r2 <- (eval :: Env -> Stmt -> IOThrowsError (Maybe Integer)) env s
                                                         case r2 of
                                                           Just v  -> return $ Just v
                                                           Nothing -> (eval :: Env -> Stmt -> IOThrowsError (Maybe Integer)) env w 
                                                 else return Nothing
  eval env w@(DoWhileStmt _ _ s e)        = do r <- (eval :: Env -> Stmt -> IOThrowsError (Maybe Integer)) env s
                                               case r of
                                                 Just v  -> return $ Just v
                                                 Nothing -> do r <- (eval :: Env -> BExpr -> IOThrowsError Bool) env e
                                                               if r
                                                                 then (eval :: Env -> Stmt -> IOThrowsError (Maybe Integer)) env w
                                                                 else return Nothing
  eval env (LocalAssignStmt _ n e)        = eval env e >>= writeStore env n >> return Nothing
  eval env (DerefStmt _ n e)              = eval env e >>= readHeap env >>= writeStore env n >> return Nothing
  eval env (AssignStmt _ e1 e2)           = do r2 <- (eval env e2)
                                               r1 <- (eval env e1)
                                               writeHeap env r1 r2
                                               return Nothing
  eval env (CallStmt _ n "alloc" [m])     = do arg <- (eval :: Env -> AExpr -> IOThrowsError Integer) env m
                                               r <- allocHeap env arg
                                               writeStore env n r
                                               return Nothing
  eval env (CallStmt _ n "CAS" [m, p, q]) = do a <- (eval :: Env -> AExpr -> IOThrowsError Integer) env m
                                               b <- (eval :: Env -> AExpr -> IOThrowsError Integer) env p
                                               c <- (eval :: Env -> AExpr -> IOThrowsError Integer) env q
                                               r <- casHeap env a b c
                                               writeStore env n (if r then 1 else 0)
                                               return Nothing
  eval env (CallStmt _ n1 n2 es)          = do f@(FunctionDeclr _ _ _ _ a s) <- getDeclr env n2 (toInteger (genericLength es))
                                               args <- mapM ((eval :: Env -> AExpr -> IOThrowsError Integer) env) es
                                               liftIO $ print args
                                               nEnv <- liftIO $ newEnv env (zip a args)
                                               r <- (eval :: Env -> Stmt -> IOThrowsError (Maybe Integer)) nEnv s
                                               writeStore env n1 (case r of
                                                                    Just v  -> v
                                                                    Nothing -> 0)
                                               return Nothing
  eval env (ReturnStmt _ Nothing)            = return $ Just 0
  eval env (ReturnStmt _ (Just e))           = (eval :: Env -> AExpr -> IOThrowsError Integer) env e >>= return . Just
  eval env (SkipStmt _)                      = return Nothing
--  show (ForkStmt _ n1 n2 es)         = n1 ++ " := fork " ++ n2 ++ "(" ++ intercalate ", " (map show es) ++ ");"
--  show (JoinStmt _ n e)              = n ++ " := join " ++ show e ++ ";"

evalAndPrint :: Env -> String -> IO ()
evalAndPrint env expr =  evalString env expr >>= putStrLn

evalString :: Env -> String -> IO String
evalString env expr = runIOThrows $ liftM show $ (liftThrows $ parseStatement expr) >>= (eval :: Env -> Stmt -> IOThrowsError (Maybe Integer)) env

until_ :: Monad m => (a -> Bool) -> m a -> (a -> m ()) -> m ()
until_ pred prompt action = do 
  result <- prompt
  if pred result then return () else action result >> until_ pred prompt action

flushStr :: String -> IO ()
flushStr str = putStr str >> hFlush stdout

readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine

runInterpreter :: IO ()
runInterpreter = do env <- emptyEnv
                    declr <- liftIO $ parseFile "examples/CASCounter.t"
                    liftIO $ newDeclr env declr
                    (until_ (== "quit") (readPrompt "> ") . evalAndPrint) env
