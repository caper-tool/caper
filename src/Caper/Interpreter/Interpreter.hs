{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FunctionalDependencies #-}

module Caper.Interpreter.Interpreter where

import Caper.Parser.AST
import Caper.Parser.Parser
import Caper.Interpreter.Environment
import Data.Maybe
import Data.List
import Control.Monad
import Control.Monad.State
#if MIN_VERSION_mtl(2,2,1)
import Control.Monad.Except
#else
import Control.Monad.Error
#endif
import Control.Concurrent
import System.IO
import Text.ParserCombinators.Parsec

class Eval a b | a -> b where
  eval :: Env -> a -> IOThrowsError b

instance Eval BExpr Bool where
  eval _ (ConstBExpr _ b)            = return b
  eval env (NotBExpr _ e)            = liftM not (eval env e)
  eval env (BinaryBExpr _ bo e1 e2)  = do
        r1 <- eval env e1
        r2 <- eval env e2
        return $ bop bo r1 r2
      where
        bop And = (&&)
        bop Or = (||)
  eval env (RBinaryBExpr _ bo e1 e2) = do
        r1 <- eval env e1
        r2 <- eval env e2
        return $ bop bo r1 r2
      where
        bop Equal = (==)
        bop NotEqual = (/=)
        bop Greater = (>)
        bop GreaterOrEqual = (>=)
        bop Less = (<)
        bop LessOrEqual = (<=)

instance Eval AExpr Integer where
  eval env (VarAExpr _  n)          = readStore env n
  eval _ (ConstAExpr _ i)           = return i
  eval env (NegAExpr _ e)           = liftM negate (eval env e)
  eval env (BinaryAExpr _ bo e1 e2) = do
        r1 <- eval env e1
        r2 <- eval env e2
        return $ bop bo r1 r2
      where
        bop Add = (+)
        bop Subtract = (-)
        bop Multiply = (*)
        bop Divide = quot

instance Eval Stmt (Maybe Integer) where
  eval _   (SeqStmt _ [])                 = return Nothing
  eval env (SeqStmt p (x:xs))             = do r <- eval env x
                                               case r of
                                                 Just v  -> return $ Just v
                                                 Nothing -> eval env (SeqStmt p xs)
  eval env (IfElseStmt _ b s1 s2)         = do r <- eval env b
                                               if r
                                                 then eval env s1
                                                 else eval env s2
  eval env w@(WhileStmt _ _ e s)          = do r <- eval env e
                                               if r
                                                 then do r2 <- eval env s
                                                         case r2 of
                                                           Just v  -> return $ Just v
                                                           Nothing -> eval env w 
                                                 else return Nothing
  eval env w@(DoWhileStmt _ _ s e)        = do r <- eval env s
                                               case r of
                                                 Just v  -> return $ Just v
                                                 Nothing -> do r <- eval env e
                                                               if r
                                                                 then eval env w
                                                                 else return Nothing
  eval env (LocalAssignStmt _ n e)        = eval env e >>= writeStore env n >> return Nothing
  eval env (DerefStmt _ n e)              = eval env e >>= readHeap env >>= writeStore env n >> return Nothing
  eval env (AssignStmt _ e1 e2)           = do r2 <- eval env e2
                                               r1 <- eval env e1
                                               writeHeap env r1 r2
                                               return Nothing
  eval env (CallStmt _ n "alloc" [m])     = do arg <- eval env m
                                               r <- allocHeap env arg
                                               when (isJust n) $ writeStore env (fromJust n) r
                                               return Nothing
  eval env (CallStmt _ n "print" [m])     = do arg <- eval env m
                                               liftIO $ print arg
                                               when (isJust n) $ writeStore env (fromJust n) 0
                                               return Nothing
  eval env (CallStmt _ n "CAS" [m, p, q]) = do a <- eval env m
                                               b <- eval env p
                                               c <- eval env q
                                               r <- casHeap env a b c
                                               when (isJust n) $ writeStore env (fromJust n) (if r then 1 else 0)
                                               return Nothing
  eval env (CallStmt _ n1 n2 es)          = do FunctionDeclr _ _ _ _ a s <- getDeclr env n2 (toInteger (genericLength es))
                                               args <- mapM (eval env) es
                                               nEnv <- liftIO $ newEnv env (zip a args)
                                               r <- eval nEnv s
                                               when (isJust n1) $ writeStore env (fromJust n1) (fromMaybe 0 r)
                                               return Nothing
  eval _ (ReturnStmt _ Nothing)           = return $ Just 0
  eval env (ReturnStmt _ (Just e))        = liftM Just (eval env e)
  eval _ (SkipStmt _)                     = return Nothing
  eval _ (AssertStmt _ _)                 = return Nothing
  eval env (ForkStmt _ n es)              = do FunctionDeclr _ _ _ _ a s <- getDeclr env n (toInteger (genericLength es))
                                               args <- mapM (eval env) es
                                               nEnv <- liftIO $ newEnv env (zip a args)
                                               liftIO $ forkIO $ runIOThrowsFork $ void (eval nEnv s)
                                               return Nothing

evalAndPrint :: Env -> String -> IO ()
evalAndPrint env expr = evalString env expr >>= putStrLn

parseStatementAux :: String -> ThrowsError Stmt
parseStatementAux str =
  case parse statementParser "" str of
    Left e  -> throwError $ Parser e
    Right r -> return r

evalString :: Env -> String -> IO String
evalString env expr = runIOThrows $ liftM show $ liftThrows (parseStatementAux expr) >>= eval env

until_ :: Monad m => (a -> Bool) -> m a -> (a -> m ()) -> m ()
until_ pred prompt action = do 
  result <- prompt
  unless (pred result) $ action result >> until_ pred prompt action

flushStr :: String -> IO ()
flushStr str = putStr str >> hFlush stdout

readPrompt :: String -> IO String
readPrompt prompt = flushStr prompt >> getLine

runInterpreter :: [String] -> IO () 
runInterpreter args =
  do env <- emptyEnv
     declr <- parseFiles args
     liftIO $ newDeclr env (functionDeclrs declr)
     (until_ (== "quit") (readPrompt "> ") . evalAndPrint) env

parseFiles :: [String] -> IO [Declr]
parseFiles []     = return []
parseFiles (x:xs) = do { declr1 <- liftIO (parseFile x); declr2 <- parseFiles xs; return $ declr1 ++ declr2 }
