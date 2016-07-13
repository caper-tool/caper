{-# LANGUAGE ExistentialQuantification, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}

-- | A module for implementing non-deterministic computation
-- lazy side-effects.  For practical purposes, the side-effects
-- must be tolerant when it comes to ordering.

module Caper.Utils.Choice where

import Control.Applicative
import Control.Monad hiding (sequence)
import Control.Monad.Trans
import Control.Monad.Trans.Maybe
import Control.Monad.Reader
import Debug.Trace
import Caper.Utils.NondetClasses
import Caper.Utils.MonadHoist

-- |'ChoiceM' datatype represents a non-deterministic choice of
-- values of type a, having (lazy) side-effects in monad m.
data ChoiceM s m a =
        Choice (ChoiceM s m a) (ChoiceM s m a)      -- A choice of two computations
        | Result a                              -- A result
        | NoChoice                              -- This computation path fails to give a result
        | Lazy (m (ChoiceM s m a))                -- This computation path requires side-effects to continue
        | forall b. OrElse (ChoiceM s m b) (ChoiceM s m b) (b -> ChoiceM s m a)
        | Cut (ChoiceM s m a)                      -- Do not roll back beyond this point
--                deriving (Functor)

instance Functor m => Functor (ChoiceM s m) where
        fmap f (Choice x y) = Choice (fmap f x) (fmap f y)
        fmap f (Result r) = Result (f r)
        fmap _ NoChoice = NoChoice
        fmap f (Lazy k) = Lazy (fmap (fmap f) k)
        fmap f (OrElse x y z) = OrElse x y (fmap f . z)
        fmap f (Cut x) = Cut (fmap f x)


-- |'Monad' instance for 'ChoiceM'.
-- Binding composes non-deterministic computations
instance Monad m => Monad (ChoiceM s m) where
        return = Result
        a >>= b = case a of
                        (Result r) -> b r
                        (Choice x y) -> Choice (x >>= b) (y >>= b)
                        NoChoice -> NoChoice
                        (Lazy l) -> Lazy $ liftM (>>= b) l
                        (OrElse x y z) -> OrElse x y (z >=> b)
                        (Cut x) -> Cut (x >>= b)
        fail s = trace s NoChoice

instance (Applicative m, Monad m) => Applicative (ChoiceM s m) where
        pure = Result
        (<*>) = ap

-- | 'MonadPlus' instance for 'ChoiceM'.
-- 'mplus' is a choice of two alternative computations
instance Monad m => MonadPlus (ChoiceM s m) where
        mzero = NoChoice
        mplus = Choice

instance (Applicative m, Monad m) => Alternative (ChoiceM s m) where
        empty = mzero
        (<|>) = mplus

-- | 'MonadOrElse' instance for 'ChoiceM'.
instance Monad m => MonadOrElse (ChoiceM s m) where
        orElse c1 c2 = OrElse c1 c2 return

instance Monad m => MonadCut (ChoiceM s m) where
        cut = Cut

-- | 'ChoiceM' is a monad transformer.
-- 'lift' records the side-effects for lazy execution
instance MonadTrans (ChoiceM s) where
        lift = Lazy . liftM Result

instance (MonadIO m) => MonadIO (ChoiceM s m) where
        liftIO = lift . liftIO

instance MonadReader r m => MonadReader r (ChoiceM s m) where
        ask = lift ask
        local m = hoist (local m)

instance MonadHoist (ChoiceM s) where
        hoist f (Choice c1 c2) = Choice (hoist f c1) (hoist f c2)
        hoist _ (Result a) = Result a
        hoist _ NoChoice = NoChoice
        hoist f (Lazy x) = Lazy (liftM (hoist f) (f x))
        hoist f (OrElse c1 c2 cont) = OrElse (hoist f c1) (hoist f c2) (hoist f . cont)
        hoist f (Cut c) = Cut (hoist f c)

instance Monad m => MonadLabel s (ChoiceM s m) where
        labelMaybe _ _ = return ()

firstChoiceT :: Monad m => ChoiceM s m a -> MaybeT m a
firstChoiceT = MaybeT . firstChoice

-- |Get the first successful choice (if any)
firstChoice :: Monad m => ChoiceM s m a -> m (Maybe a)
firstChoice c = firstChoice' c (return Nothing)
{-
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
-}

firstChoice' :: Monad m => ChoiceM s m a -> m (Maybe a) -> m (Maybe a)
firstChoice' (Result a) _ = return $ Just a
firstChoice' NoChoice bt = bt
firstChoice' (Choice x y) bt = firstChoice' x (firstChoice' y bt) 
firstChoice' (Lazy x) bt = x >>= \r -> firstChoice' r bt
firstChoice' (OrElse x y z) bt = do
                        cx <- firstChoice' x (return Nothing)
                        case cx of
                                (Just r) -> firstChoice' (z r) bt
                                Nothing -> firstChoice' (y >>= z) bt
firstChoice' (Cut x) bt = firstChoice' x (return Nothing)


-- |Get the first choice that doesn't require any side-effects
-- to evaluate.
-- BROKEN FOR OrElse, Cut
firstAvailableChoice :: ChoiceM s m a -> Maybe a
firstAvailableChoice (Result a) = Just a
firstAvailableChoice (Choice x y) = case firstAvailableChoice x of
                                (Just cx) -> Just cx
                                Nothing -> firstAvailableChoice y
firstAvailableChoice _ = Nothing

-- |Get the first choice, if any, (executing side-effects as 
-- necessary).  The choice is pared from the returned ChoiceM.
-- Only side-effects necessary to discover the first choice are
-- executed.  DOES NOT RESPECT CUTS
nextChoice :: Monad m => ChoiceM s m a -> m (Maybe a, ChoiceM s m a)
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
nextChoice (Cut x) = nextChoice x

-- |Get all choices, performing side-effects as necessary
-- DOES NOT RESPECT CUTS
allChoices :: Monad m => ChoiceM s m a -> m [a]
allChoices c = do
                (cx, rx) <- nextChoice c
                case cx of
                        (Just x) -> do
                                rs <- allChoices rx
                                return (x : rs)
                        _ -> return []

-- |Get the first n choices, performing side-effects as necessary
-- DOES NOT RESPECT CUTS
takeChoices :: Monad m => Int -> ChoiceM s m a -> m [a]
takeChoices 0 _ = return []
takeChoices n c = do
                (cx, rx) <- nextChoice c
                case cx of
                        (Just x) -> do
                                rs <- takeChoices (n - 1) rx
                                return (x : rs)
                        _ -> return []




