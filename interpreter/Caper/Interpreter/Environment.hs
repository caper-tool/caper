{-# LANGUAGE CPP #-}
module Caper.Interpreter.Environment where

import Caper.Parser.AST
import Data.IORef
import Data.List
import Data.Maybe
import Control.Concurrent
import Control.Monad
import Control.Monad.Trans
#if MIN_VERSION_mtl(2,2,1)
import Control.Monad.Except
#else
import Control.Monad.Error
#endif
import Text.ParserCombinators.Parsec

data EnvError = NotFunction String
              | UnboundVar String
              | NotAllocated String Integer
              | NonPositiveAlloc
              | NoThread Integer
              | Parser ParseError
              | Default String

instance Show EnvError where
  show (NotFunction name)               = "Unknown function " ++ name
  show (UnboundVar name)                = "Unknown variable " ++ name
  show (NotAllocated operation address) = "Cannot perform " ++ operation ++ " on non allocated heap address " ++ show address
  show NonPositiveAlloc                 = "Cannot call alloc with a non positive argument"
  show (NoThread tid)                   = "Cannot perform join on non existing thread " ++ show tid
  show (Parser message)                 = "Parse error at " ++ show message
  show (Default message)                = show message

type ThrowsError = Either EnvError
#if MIN_VERSION_mtl(2,2,1)
type IOThrowsError = ExceptT EnvError IO
runIOThrowsError = runExceptT
#else
type IOThrowsError = ErrorT EnvError IO
runIOThrowsError = runErrorT
instance Error EnvError where
  noMsg = Default "An error has occurred"
  strMsg = Default
#endif
runIOThrowsError :: IOThrowsError a -> IO (ThrowsError a)


trapError action = catchError action (return . show)

extractValue :: ThrowsError a -> a
extractValue (Right val) = val
extractValue (Left err) = error (show err)

liftThrows :: ThrowsError a -> IOThrowsError a
liftThrows (Left err) = throwError err
liftThrows (Right val) = return val

runIOThrows :: IOThrowsError String -> IO String
runIOThrows action = liftM extractValue (runIOThrowsError (trapError action))

trapErrorFork action = catchError action (\_a -> return ())

runIOThrowsFork :: IOThrowsError () -> IO ()
runIOThrowsFork action = liftM extractValue (runIOThrowsError (trapErrorFork action))

type Heap = MVar [(Integer, Integer)]
type Store = [(String, Integer)]
type Env = IORef (Heap, Store, [FunctionDeclr])

heapEnv :: (Heap, Store, [FunctionDeclr]) -> Heap
heapEnv (h, _, _) = h

storeEnv :: (Heap, Store, [FunctionDeclr]) -> Store
storeEnv (_, s, _) = s

declrEnv :: (Heap, Store, [FunctionDeclr]) -> [FunctionDeclr]
declrEnv (_, _, d) = d

emptyEnv :: IO Env
emptyEnv =
  do heap <- newMVar []
     newIORef (heap, [], [])

newEnv :: Env -> Store -> IO Env
newEnv envRef newStore =
  do env <- liftIO $ readIORef envRef
     newIORef (heapEnv env, newStore, declrEnv env)

printEnv :: Env -> IO ()
printEnv envRef =
  do env <- liftIO $ readIORef envRef
     liftIO $ print (storeEnv env)
     heap  <- liftIO $ takeMVar $ heapEnv env
     liftIO $ print heap
     liftIO $ putMVar (heapEnv env) heap
     return ()

readHeap :: Env -> Integer -> IOThrowsError Integer
readHeap envRef n =
  do env   <- liftIO $ readIORef envRef
     heap  <- liftIO $ takeMVar $ heapEnv env
     case lookup n heap of
       Just v  -> liftIO (putMVar (heapEnv env) heap) >> return v
       Nothing -> liftIO (putMVar (heapEnv env) heap) >> throwError (NotAllocated "read" n)

writeHeap :: Env -> Integer -> Integer -> IOThrowsError ()
writeHeap envRef n m =
  do env   <- liftIO $ readIORef envRef
     heap  <- liftIO $ takeMVar $ heapEnv env
     case lookup n heap of
       Just _v -> void (liftIO (putMVar (heapEnv env) ((n, m) : filter (\a -> fst a /= n) heap)))
       Nothing -> liftIO (putMVar (heapEnv env) heap) >> throwError (NotAllocated "wrote" n)

casHeap :: Env -> Integer -> Integer -> Integer -> IOThrowsError Bool
casHeap envRef n m p =
  do env   <- liftIO $ readIORef envRef
     heap  <- liftIO $ takeMVar $ heapEnv env
     case lookup n heap of
       Just _v -> liftIO $ if (n, m) `elem` heap
                             then putMVar (heapEnv env) ((n, p) : filter (\a -> fst a /= n) heap) >> return True
                             else putMVar (heapEnv env) heap >> return False
       Nothing -> liftIO (putMVar (heapEnv env) heap) >> throwError (NotAllocated "CAS" n)

allocHeap :: Env -> Integer -> IOThrowsError Integer
allocHeap envRef n =
  do env   <- liftIO $ readIORef envRef
     heap  <- liftIO $ takeMVar $ heapEnv env
     if n > 0
       then liftIO (putMVar (heapEnv env) $ heap ++ map (\a -> (a, 0)) (genericTake n [(newAddress heap)..])) >> return (newAddress heap)
       else liftIO (putMVar (heapEnv env) heap) >> throwError NonPositiveAlloc
     where newAddress l = toInteger (genericLength l + 1)

readStore :: Env -> String -> IOThrowsError Integer
readStore envRef var =
  do env <- liftIO $ readIORef envRef
     case lookup var (storeEnv env) of
       Just v  -> return v
       Nothing -> throwError $ UnboundVar var

writeStore :: Env -> String -> Integer -> IOThrowsError ()
writeStore envRef var n =
  do env    <- liftIO $ readIORef envRef
     when (isNothing $ lookup var (storeEnv env)) (liftIO $ writeIORef envRef (heapEnv env, (var, 0) : storeEnv env, declrEnv env))
     void (liftIO $ writeIORef envRef (heapEnv env, (var, n) : filter (\ a -> fst a /= var) (storeEnv env), declrEnv env))

getDeclr :: Env -> String -> Integer -> IOThrowsError FunctionDeclr
getDeclr envRef name nargs =
  do env <- liftIO $ readIORef envRef
     let f = filter (\a -> isFunction a name nargs) (declrEnv env)
     when (null f) (throwError $ NotFunction name)
     return (head f)
  where isFunction (FunctionDeclr _ fname _ _ args _) n m = fname == n && toInteger (genericLength args) == m

newDeclr :: Env -> [FunctionDeclr] -> IO ()
newDeclr envRef declr =
  liftIO $ do env <- readIORef envRef
              writeIORef envRef (heapEnv env, storeEnv env, declr ++ declrEnv env)
