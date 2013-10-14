module Environment where

import AST
import Data.IORef
import Control.Concurrent
import Control.Monad.Trans
import Data.List
import Control.Monad.Error
import System.IO

data EnvError = NumArgs String Integer Integer
              | NotFunction String
              | UnboundVar String
              | RedeclarationVar String
              | NotAllocated String Integer
              | NonPositiveAlloc
              | Default String

instance Show EnvError where
  show (NumArgs name expected found)    = "Expected " ++ show expected ++ " arguments, but found " ++ show found ++ ", in function " ++ name
  show (NotFunction name)               = "Unknown function " ++ name
  show (UnboundVar name)                = "Unknown variable " ++ name
  show (RedeclarationVar name)          = "Variable " ++ name ++ " was previously declared"
  show (NotAllocated operation address) = "Cannot perform " ++ operation ++ " on non allocated heap address " ++ show address
  show (NonPositiveAlloc)               = "Cannot call alloc with a non positive argument"

instance Error EnvError where
  noMsg = Default "An error has occurred"
  strMsg = Default

type ThrowsError = Either EnvError
type IOThrowsError = ErrorT EnvError IO

trapError action = catchError action (return . show)

extractValue :: ThrowsError a -> a
extractValue (Right val) = val

liftThrows :: ThrowsError a -> IOThrowsError a
liftThrows (Left err) = throwError err
liftThrows (Right val) = return val

runIOThrows :: IOThrowsError String -> IO String
runIOThrows action = runErrorT (trapError action) >>= return . extractValue

type Heap = MVar [(Integer, Integer)]
type Store = [(String, Integer)]
type Env = IORef (Heap, Store, [Declr])

heapEnv :: (Heap, Store, [Declr]) -> Heap
heapEnv (h, _, _) = h

storeEnv :: (Heap, Store, [Declr]) -> Store
storeEnv (_, s, _) = s

declrEnv :: (Heap, Store, [Declr]) -> [Declr]
declrEnv (_, _, d) = d

emptyEnv :: IO Env
emptyEnv =
  do heap <- newMVar [(1, 2)]
     env  <- newIORef (heap, [("a",1)], [])
     return env

readHeap :: Env -> Integer -> IOThrowsError Integer
readHeap envRef n =
  do env   <- liftIO $ readIORef envRef
     heap  <- liftIO $ takeMVar $ heapEnv env
     case lookup n heap of
       Just v  -> liftIO $ putMVar (heapEnv env) heap >> return v
       Nothing -> (liftIO $ putMVar (heapEnv env) heap) >> throwError (NotAllocated "read" n)

writeHeap :: Env -> Integer -> Integer -> IOThrowsError ()
writeHeap envRef n m =
  do env   <- liftIO $ readIORef envRef
     heap  <- liftIO $ takeMVar $ heapEnv env
     case lookup n heap of
       Just v  -> liftIO $ putMVar (heapEnv env) ((n, m) : filter (\a -> (fst a) /= n) heap) >> return ()
       Nothing -> (liftIO $ putMVar (heapEnv env) heap) >> throwError (NotAllocated "wrote" n)

casHeap :: Env -> Integer -> Integer -> Integer -> IOThrowsError Bool
casHeap envRef n m p =
  do env   <- liftIO $ readIORef envRef
     heap  <- liftIO $ takeMVar $ heapEnv env
     case lookup n heap of
       Just v  -> liftIO $ if elem (n, m) heap
                             then putMVar (heapEnv env) ((n, p) : filter (\a -> (fst a) /= n) heap) >> return True
                             else putMVar (heapEnv env) heap >> return False
       Nothing -> (liftIO $ putMVar (heapEnv env) heap) >> throwError (NotAllocated "CAS" n)

allocHeap :: Env -> Integer -> IOThrowsError Integer
allocHeap envRef n =
  do env   <- liftIO $ readIORef envRef
     heap  <- liftIO $ takeMVar $ heapEnv env
     liftIO $ print heap
     if n > 0
       then (liftIO $ putMVar (heapEnv env) $ heap ++ (map (\a -> (a, 0)) (genericTake n [(newAddress heap)..]))) >> return (newAddress heap)
       else (liftIO $ putMVar (heapEnv env) heap) >> (throwError NonPositiveAlloc)
     where newAddress l = toInteger (genericLength l + 1)

readStore :: Env -> String -> IOThrowsError Integer
readStore envRef var =
  do env <- liftIO $ readIORef envRef
     case lookup var (storeEnv env) of
       Just v  -> return v
       Nothing -> throwError $ UnboundVar var

writeStore :: Env -> String -> Integer -> IOThrowsError ()
writeStore envRef var n =
  do env <- liftIO $ readIORef envRef
     liftIO $ print (storeEnv env)
     case lookup var (storeEnv env) of
       Just v  -> liftIO $ writeIORef envRef (heapEnv env, ((var, n) : filter (\a -> (fst a) /= var) (storeEnv env)), declrEnv env) >> return ()
       Nothing -> throwError $ UnboundVar var

varStore :: Env -> String -> IOThrowsError ()
varStore envRef var =
  do env <- liftIO $ readIORef envRef
     liftIO $ print (storeEnv env)
     case lookup var (storeEnv env) of
       Just v  -> throwError $ RedeclarationVar var
       Nothing -> liftIO $ writeIORef envRef (heapEnv env, (var, 0):(storeEnv env), declrEnv env) >> return ()
