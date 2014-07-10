{-# LANGUAGE RankNTypes, MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable, FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}
import Prelude hiding (catch,mapM,sequence,foldl,mapM_)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Exception
import Data.Foldable
import Data.Traversable
import Control.Monad.State hiding (sequence)
import Control.Monad hiding (sequence)
import Control.Monad.List
import Control.Applicative
import Control.Monad.Trans.Maybe

incrState :: Monad m => StateT Integer m ()
incrState = modify (+1)

doubleState :: Monad m => StateT Integer m ()
doubleState = modify (*2)

divFour :: Monad m => StateT Integer m Bool
divFour = get >>= (\x -> return $ x `div` 4 == 0)

divFourFail :: (Monad m, MonadPlus m) => StateT Integer m ()
divFourFail = do
                x <- get
                if (x `mod` 4 == 0) then mzero else return ()

test :: (Monad m, MonadPlus m, MonadIO m) => StateT Integer m Integer
test = do
        incrState `mplus` doubleState
        x <- get
        liftIO $ putStrLn (show x)
        divFourFail
        return x `mplus` test

runTest :: ListT IO Integer
runTest = execStateT test 1

runTest' :: IO [Integer]
runTest' = do
        x <- runListT runTest -- $ mapListT (fmap $ take 10) runTest
        return x


--data Choice a = Choice (Choice a) (Choice a) | Result a | NoChoice

data ChoiceM m a = Choice (ChoiceM m a) (ChoiceM m a) | Result a | NoChoice | Lazy (m (ChoiceM m a)) deriving (Functor)

firstChoice :: Monad m => ChoiceM m a -> m (Maybe a)
firstChoice (Result a) = return $ Just a
firstChoice NoChoice = return Nothing
firstChoice (Choice x y) = do
                                cx <- firstChoice x
                                case cx of
                                        (Just _) -> return cx
                                        Nothing -> firstChoice y
firstChoice (Lazy x) = x >>= firstChoice

firstAvailableChoice :: ChoiceM m a -> Maybe a
firstAvailableChoice (Result a) = Just a
firstAvailableChoice (Choice x y) = case firstAvailableChoice x of
                                (Just cx) -> Just cx
                                Nothing -> firstAvailableChoice y
firstAvailableChoice _ = Nothing

nextChoice :: Monad m => ChoiceM m a -> m (Maybe a, ChoiceM m a)
nextChoice (Result a) = return (Just a, NoChoice)
nextChoice NoChoice = return (Nothing, NoChoice)
nextChoice (Choice x y) = do
                                (cx, rx) <- nextChoice x
                                case cx of
                                        (Just _) -> return (cx, Choice rx y)
                                        Nothing -> nextChoice y
nextChoice (Lazy l) = l >>= nextChoice

allChoices :: Monad m => ChoiceM m a -> m [a]
allChoices c = do
                (cx, rx) <- nextChoice c
                case cx of
                        (Just x) -> do
                                rs <- allChoices rx
                                return (x : rs)
                        _ -> return []

takeChoices :: Monad m => Int -> ChoiceM m a -> m [a]
takeChoices 0 _ = return []
takeChoices n c = do
                (cx, rx) <- nextChoice c
                case cx of
                        (Just x) -> do
                                rs <- takeChoices (n - 1) rx
                                return (x : rs)
                        _ -> return []


instance Monad m => Monad (ChoiceM m) where
        return = Result
        a >>= b = case a of
                        (Result r) -> b r
                        (Choice x y) -> Choice (x >>= b) (y >>= b)
                        NoChoice -> NoChoice
                        (Lazy l) -> Lazy $ liftM (>>= b) l

instance Monad m => MonadPlus (ChoiceM m) where
        mzero = NoChoice
        mplus c1 c2 = Choice c1 c2

instance MonadTrans ChoiceM where
        lift = Lazy . (liftM Result)

instance (MonadIO m) => MonadIO (ChoiceM m) where
        liftIO = lift . liftIO

lazyRunTest :: ChoiceM IO Integer
lazyRunTest = execStateT test 1

lazyRunTest' :: IO ([Maybe Integer])
lazyRunTest' = do
                (x1, c1) <- nextChoice lazyRunTest
                (x2, c2) <- nextChoice c1
                return [x1,x2]
