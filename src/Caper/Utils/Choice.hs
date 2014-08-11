{-# LANGUAGE ExistentialQuantification #-}

-- | A module for implementing non-deterministic computation
-- lazy side-effects.  For practical purposes, the side-effects
-- must be tolerant when it comes to ordering.

module Caper.Utils.Choice where

import Control.Monad hiding (sequence)
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Debug.Trace
import Caper.Utils.NondetClasses
import Caper.Utils.MonadHoist

-- |Lift a 'Maybe' into an arbitrary non-deterministic monad.
liftMaybe :: (MonadPlus m) => Maybe a -> m a
liftMaybe (Just x) = return x
liftMaybe Nothing = mzero

-- ChoiceM datatype represents a non-determinstic choice of
-- values of type a, having (lazy) side-effects in monad m.
data ChoiceM m a =
        Choice (ChoiceM m a) (ChoiceM m a)      -- A choice of two computations
        | Result a                              -- A result
        | NoChoice                              -- This computation path fails to give a result
        | Lazy (m (ChoiceM m a))                -- This computation path requires side-effects to continue
        | forall b. OrElse (ChoiceM m b) (ChoiceM m b) (b -> ChoiceM m a)
--                deriving (Functor)

instance Functor m => Functor (ChoiceM m) where
        fmap f (Choice x y) = Choice (fmap f x) (fmap f y)
        fmap f (Result r) = Result (f r)
        fmap _ NoChoice = NoChoice
        fmap f (Lazy k) = Lazy (fmap (fmap f) k)
        fmap f (OrElse x y z) = OrElse x y (fmap f . z)

-- Monad instance for ChoiceM.
-- Binding composes non-deterministic computations
instance Monad m => Monad (ChoiceM m) where
        return = Result
        a >>= b = case a of
                        (Result r) -> b r
                        (Choice x y) -> Choice (x >>= b) (y >>= b)
                        NoChoice -> NoChoice
                        (Lazy l) -> Lazy $ liftM (>>= b) l
                        (OrElse x y z) -> OrElse x y (z >=> b)
        fail s = trace s NoChoice

-- MonadPlus instance for ChoiceM.
-- mplus is a choice of two alternative computations
instance Monad m => MonadPlus (ChoiceM m) where
        mzero = NoChoice
        mplus = Choice

-- MonadOrElse instance for ChoiceM.
instance Monad m => MonadOrElse (ChoiceM m) where
        orElse c1 c2 = OrElse c1 c2 return

-- ChoiceM is a monad transformer.
-- lift records the side-effects for lazy execution
instance MonadTrans ChoiceM where
        lift = Lazy . liftM Result

instance (MonadIO m) => MonadIO (ChoiceM m) where
        liftIO = lift . liftIO

instance MonadHoist ChoiceM where
        hoist f (Choice c1 c2) = Choice (hoist f c1) (hoist f c2)
        hoist _ (Result a) = Result a
        hoist _ NoChoice = NoChoice
        hoist f (Lazy x) = Lazy (liftM (hoist f) (f x))
        hoist f (OrElse c1 c2 cont) = OrElse (hoist f c1) (hoist f c2) (hoist f . cont)


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
firstChoice (OrElse x y z) = do
                                cx <- firstChoice x
                                case cx of
                                        (Just r) -> firstChoice (z r)
                                        Nothing -> do
                                                cy <- firstChoice y
                                                case cy of
                                                        (Just r) -> firstChoice (z r)
                                                        Nothing -> return Nothing

-- Get the first choice that doesn't require any side-effects
-- to evaluate.
-- BROKEN FOR OrElse
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
nextChoice (OrElse x y z) = do
                        (cx, rx) <- nextChoice x
                        case cx of
                                (Just r) -> do
                                        (cz, rz) <- nextChoice (z r)
                                        case cz of
                                                (Just _) -> return (cz, Choice rz (rx >>= z))
                                                Nothing -> nextChoice (rx >>= z)
                                Nothing -> nextChoice (y >>= z)

-- Get all choices, performing side-effects as necessary
allChoices :: Monad m => ChoiceM m a -> m [a]
allChoices c = do
                (cx, rx) <- nextChoice c
                case cx of
                        (Just x) -> do
                                rs <- allChoices rx
                                return (x : rs)
                        _ -> return []

-- Get the first n choices, performing side-effects as necessary
takeChoices :: Monad m => Int -> ChoiceM m a -> m [a]
takeChoices 0 _ = return []
takeChoices n c = do
                (cx, rx) <- nextChoice c
                case cx of
                        (Just x) -> do
                                rs <- takeChoices (n - 1) rx
                                return (x : rs)
                        _ -> return []




