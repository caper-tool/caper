{-# LANGUAGE DeriveFunctor #-}

-- A module for implementing non-deterministic computation
-- lazy side-effects.  For practical purposes, the side-effects
-- must be tolerant when it comes to ordering.

module Choice where

import Control.Monad hiding (sequence)
import Control.Monad.Trans
import Control.Monad.Trans.Maybe

-- ChoiceM datatype represents a non-determinstic choice of
-- values of type a, having (lazy) side-effects in monad m.
data ChoiceM m a =
        Choice (ChoiceM m a) (ChoiceM m a)      -- A choice of two computations
        | Result a                              -- A result
        | NoChoice                              -- This computation path fails to give a result
        | Lazy (m (ChoiceM m a))                -- This computation path requires side-effects to continue
                deriving (Functor)

-- Monad instance for ChoiceM.
-- Binding composes non-deterministic computations
instance Monad m => Monad (ChoiceM m) where
        return = Result
        a >>= b = case a of
                        (Result r) -> b r
                        (Choice x y) -> Choice (x >>= b) (y >>= b)
                        NoChoice -> NoChoice
                        (Lazy l) -> Lazy $ liftM (>>= b) l
        fail _ = NoChoice

-- MonadPlus instance for ChoiceM.
-- mplus is a choice of two alternative computations
instance Monad m => MonadPlus (ChoiceM m) where
        mzero = NoChoice
        mplus c1 c2 = Choice c1 c2

-- ChoiceM is a monad transformer.
-- lift records the side-effects for lazy execution
instance MonadTrans ChoiceM where
        lift = Lazy . (liftM Result)

instance (MonadIO m) => MonadIO (ChoiceM m) where
        liftIO = lift . liftIO


firstChoiceT :: Monad m => ChoiceM m a -> MaybeT m a
firstChoiceT = MaybeT . firstChoice

-- Get the first successful choice (if any)
firstChoice :: Monad m => ChoiceM m a -> m (Maybe a)
firstChoice (Result a) = return $ Just a
firstChoice NoChoice = return Nothing
firstChoice (Choice x y) = do
                                cx <- firstChoice x
                                case cx of
                                        (Just _) -> return cx
                                        Nothing -> firstChoice y
firstChoice (Lazy x) = x >>= firstChoice

-- Get the first choice that doesn't require any side-effects
-- to evaluate.
firstAvailableChoice :: ChoiceM m a -> Maybe a
firstAvailableChoice (Result a) = Just a
firstAvailableChoice (Choice x y) = case firstAvailableChoice x of
                                (Just cx) -> Just cx
                                Nothing -> firstAvailableChoice y
firstAvailableChoice _ = Nothing

-- Get the first choice, if any, (executing side-effects as 
-- necessary).  The choice is pared from the returned ChoiceM.
-- Only side-effects necessary to discover the first choice are
-- executed.
nextChoice :: Monad m => ChoiceM m a -> m (Maybe a, ChoiceM m a)
nextChoice (Result a) = return (Just a, NoChoice)
nextChoice NoChoice = return (Nothing, NoChoice)
nextChoice (Choice x y) = do
                                (cx, rx) <- nextChoice x
                                case cx of
                                        (Just _) -> return (cx, Choice rx y)
                                        Nothing -> nextChoice y
nextChoice (Lazy l) = l >>= nextChoice

-- Get all choices, performing side-effects as necessary
allChoices :: Monad m => ChoiceM m a -> m [a]
allChoices c = do
                (cx, rx) <- nextChoice c
                case cx of
                        (Just x) -> do
                                rs <- allChoices rx
                                return (x : rs)
                        _ -> return []

-- Get the first n choices, peforming side-effects as necessary
takeChoices :: Monad m => Int -> ChoiceM m a -> m [a]
takeChoices 0 _ = return []
takeChoices n c = do
                (cx, rx) <- nextChoice c
                case cx of
                        (Just x) -> do
                                rs <- takeChoices (n - 1) rx
                                return (x : rs)
                        _ -> return []




