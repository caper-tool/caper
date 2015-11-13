{-# LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances #-}
{- |This module provides a monad for implementing combined angelic and
    demonic choice, with state and lazy side-effects.  Different ways
    of running this monad will execute side-effects in the underlying
    monad in different orders (perhaps even concurrently), so it is
    often important that these effects can be reordered without
    compromising the result.
-}

module Caper.Utils.Alternating where

import Control.Applicative
import Control.Monad hiding (sequence)
import Control.Monad.Trans
--import Control.Monad.Trans.Maybe
import Control.Monad.Reader
import Control.Monad.State

import Debug.Trace

import Caper.Utils.NondetClasses
import Caper.Utils.MonadHoist

data AlternatingT m a where
    NoChoice :: AlternatingT m a
    Result :: a -> AlternatingT m a
    Lazy :: m (AlternatingT m a) -> AlternatingT m a
    AngelicChoice :: AlternatingT m a -> AlternatingT m a -> AlternatingT m a
    DemonicChoice :: AlternatingT m a -> AlternatingT m a -> AlternatingT m a
    OrElse :: AlternatingT m b -> AlternatingT m b -> (b -> AlternatingT m a) -> AlternatingT m a
    Cut :: AlternatingT m a -> AlternatingT m a
    Success :: AlternatingT m a

instance Functor m => Functor (AlternatingT m) where
    fmap _ NoChoice = NoChoice
    fmap f (Result r) = Result (f r)
    fmap f (Lazy k) = Lazy (fmap (fmap f) k)
    fmap f (AngelicChoice x y) = AngelicChoice (fmap f x) (fmap f y)
    fmap f (DemonicChoice x y) = DemonicChoice (fmap f x) (fmap f y)
    fmap f (OrElse x y z) = OrElse x y (fmap f . z)
    fmap f (Cut x) = Cut (fmap f x)
    fmap _ Success = Success
    
instance Monad m => Monad (AlternatingT m) where
    return = Result
    a >>= b = case a of
            NoChoice -> NoChoice
            (Result r) -> b r
            (Lazy k) -> Lazy $ liftM (>>= b) k
            (AngelicChoice x y) -> AngelicChoice (x >>= b) (y >>= b)
            (DemonicChoice x y) -> DemonicChoice (x >>= b) (y >>= b)
            (OrElse x y z) -> OrElse x y (z >=> b)
            (Cut x) -> Cut (x >>= b)
            Success -> Success
    fail s = trace s NoChoice
    
instance (Applicative m, Monad m) => Applicative (AlternatingT m) where
    pure = Result
    (<*>) = ap

instance Monad m => MonadPlus (AlternatingT m) where
    mzero = NoChoice
    mplus = AngelicChoice
    
instance (Applicative m, Monad m) => Alternative (AlternatingT m) where
    empty = mzero
    (<|>) = mplus
    
instance Monad m => MonadOrElse (AlternatingT m) where
    orElse c1 c2 = OrElse c1 c2 return

instance Monad m => MonadCut (AlternatingT m) where
    cut = Cut
    
instance MonadTrans (AlternatingT) where
    lift = Lazy . liftM return

instance MonadHoist (AlternatingT) where
    hoist _ NoChoice = NoChoice
    hoist _ (Result r) = Result r
    hoist f (Lazy k) = Lazy (liftM (hoist f) (f k)) 
    hoist f (AngelicChoice x y) = AngelicChoice (hoist f x) (hoist f y)
    hoist f (DemonicChoice x y) = DemonicChoice (hoist f x) (hoist f y)
    hoist f (OrElse x y z) = OrElse (hoist f x) (hoist f y) (hoist f . z)
    hoist f (Cut x) = Cut (hoist f x)
    hoist f Success = Success

instance MonadIO m => MonadIO (AlternatingT m) where
    liftIO = lift . liftIO
    
instance MonadReader r m => MonadReader r (AlternatingT m) where
    ask = lift ask
    local m = hoist (local m)

    
instance Monad m => MonadDemonic (AlternatingT m) where
    (<#>) = DemonicChoice
    succeed = Success
    
runAlternatingT' :: Monad m => AlternatingT m a -> m (Maybe [a]) -> m (Maybe [a])
runAlternatingT' NoChoice bt = bt
runAlternatingT' (Result a) _ = return $ Just [a]
runAlternatingT' (Lazy k) bt = do
                            a <- k
                            runAlternatingT' a bt 
runAlternatingT' (AngelicChoice x y) bt = runAlternatingT' x (runAlternatingT' y bt)
runAlternatingT' (DemonicChoice x y) bt = do
                            r0 <- runAlternatingT' x (return Nothing)
                            case r0 of
                                Nothing -> bt
                                Just rs -> do
                                    r1 <- runAlternatingT' y (return Nothing)
                                    case r1 of
                                        Nothing -> bt
                                        Just rs' -> return (Just (rs ++ rs'))
runAlternatingT' (OrElse x y z) bt = do
                        r0 <- runAlternatingT' x (return Nothing)
                        case r0 of
                            Nothing -> runAlternatingT' (y >>= z) bt
                            Just rs -> do
                                r1 <- foo [runAlternatingT' (z b) (return Nothing) | b <- rs] []
                                case r1 of
                                    Nothing -> bt
                                    rs' -> return rs'  
        where
            foo [] rs = return (Just rs)
            foo (a:aa) rs = do
                r0 <- a
                case r0 of
                    Nothing -> return Nothing
                    Just rs' -> foo aa (rs ++ rs')  
runAlternatingT' (Cut x) bt = runAlternatingT' x (return Nothing)
runAlternatingT' Success bt = return (Just [])

runAlternatingT :: Monad m => AlternatingT m a -> m (Maybe [a])
runAlternatingT a = runAlternatingT' a (return Nothing)
