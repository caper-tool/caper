{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}

module Caper.Interpreter.Interpreter where

import Caper.Parser.AST
import Caper.Parser.Parser
import Caper.Interpreter.Environment
import Data.Maybe
import Data.List
import Control.Monad.State
import Control.Monad.Error
import Control.Concurrent
import System.IO
import Text.ParserCombinators.Parsec

class Eval a b where
  eval :: Env -> a -> IOThrowsError b

instance Eval BExpr Bool where
  eval _ (ConstBExpr _ b)                        = return b
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
                                                      return $ r1 <= r2

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
  eval _   (SeqStmt _ [])                 = return Nothing
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
                                               when (isJust n) $ writeStore env (fromJust n) r
                                               return Nothing
  eval env (CallStmt _ n "print" [m])     = do arg <- (eval :: Env -> AExpr -> IOThrowsError Integer) env m
                                               liftIO $ print arg
                                               when (isJust n) $ writeStore env (fromJust n) 0
                                               return Nothing
  eval env (CallStmt _ n "CAS" [m, p, q]) = do a <- (eval :: Env -> AExpr -> IOThrowsError Integer) env m
                                               b <- (eval :: Env -> AExpr -> IOThrowsError Integer) env p
                                               c <- (eval :: Env -> AExpr -> IOThrowsError Integer) env q
                                               r <- casHeap env a b c
                                               when (isJust n) $ writeStore env (fromJust n) (if r then 1 else 0)
                                               return Nothing
  eval env (CallStmt _ n1 n2 es)          = do FunctionDeclr _ _ _ _ a s <- getDeclr env n2 (toInteger (genericLength es))
                                               args <- mapM ((eval :: Env -> AExpr -> IOThrowsError Integer) env) es
                                               nEnv <- liftIO $ newEnv env (zip a args)
                                               r <- (eval :: Env -> Stmt -> IOThrowsError (Maybe Integer)) nEnv s
                                               when (isJust n1) $ writeStore env (fromJust n1) (case r of
                                                                                                  Just v  -> v
                                                                                                  Nothing -> 0)
                                               return Nothing
  eval _ (ReturnStmt _ Nothing)           = return $ Just 0
  eval env (ReturnStmt _ (Just e))        = (eval :: Env -> AExpr -> IOThrowsError Integer) env e >>= return . Just
  eval _ (SkipStmt _)                     = return Nothing
  eval _ (AssertStmt _ _)                 = return Nothing
  eval env (ForkStmt _ n es)              = do FunctionDeclr _ _ _ _ a s <- getDeclr env n (toInteger (genericLength es))
                                               args <- mapM ((eval :: Env -> AExpr -> IOThrowsError Integer) env) es
                                               nEnv <- liftIO $ newEnv env (zip a args)
                                               liftIO $ forkIO $ runIOThrowsFork $ ((eval :: Env -> Stmt -> IOThrowsError (Maybe Integer)) nEnv s) >> return ()
                                               return Nothing

evalAndPrint :: Env -> String -> IO ()
evalAndPrint env expr = evalString env expr >>= putStrLn

parseStatementAux :: String -> ThrowsError Stmt
parseStatementAux str =
  case parse statementParser "" str of
    Left e  -> throwError $ Parser e
    Right r -> return r

evalString :: Env -> String -> IO String
evalString env expr = runIOThrows $ liftM show $ (liftThrows $ parseStatementAux expr) >>= (eval :: Env -> Stmt -> IOThrowsError (Maybe Integer)) env

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
                    declr <- liftIO $ parseFile "../examples/CASLock.t"
                    liftIO $ newDeclr env (functionDeclrs declr)
                    (until_ (== "quit") (readPrompt "> ") . evalAndPrint) env
