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
import Control.Monad.Reader

import Debug.Trace

import Caper.Utils.NondetClasses
import Caper.Utils.MonadHoist
import Caper.Utils.Failure

data AlternatingT e m a where
    NoChoice :: AlternatingT e m a
    Result :: a -> AlternatingT e m a
    Lazy :: m (AlternatingT e m a) -> AlternatingT e m a
    AngelicChoice :: AlternatingT e m a -> AlternatingT e m a -> AlternatingT e m a
    DemonicChoice :: AlternatingT e m a -> AlternatingT e m a -> AlternatingT e m a
    OrElse :: AlternatingT e m b -> AlternatingT e m b -> (b -> AlternatingT e m a) -> AlternatingT e m a
    Cut :: AlternatingT e m a -> AlternatingT e m a
    Success :: AlternatingT e m a
    Failure :: e -> AlternatingT e m a
    Retry :: AlternatingT e m a -> (e -> Maybe (AlternatingT e m a)) -> AlternatingT e m a

instance Functor m => Functor (AlternatingT e m) where
    fmap _ NoChoice = NoChoice
    fmap f (Result r) = Result (f r)
    fmap f (Lazy k) = Lazy (fmap (fmap f) k)
    fmap f (AngelicChoice x y) = AngelicChoice (fmap f x) (fmap f y)
    fmap f (DemonicChoice x y) = DemonicChoice (fmap f x) (fmap f y)
    fmap f (OrElse x y z) = OrElse x y (fmap f . z)
    fmap f (Cut x) = Cut (fmap f x)
    fmap _ Success = Success
    fmap _ (Failure e) = Failure e
    fmap f (Retry x h) = Retry (fmap f x) (fmap (fmap (fmap f)) h)
    
instance Monad m => Monad (AlternatingT e m) where
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
            Failure e -> Failure e
            Retry x h -> Retry (x >>= b) (fmap (fmap (>>= b)) h)
    fail s = trace s NoChoice

instance Failure e (AlternatingT e m) where
    failure = Failure

instance (Monad m) => OnFailure e (AlternatingT e m) where
    retry = Retry
    
instance (Applicative m, Monad m) => Applicative (AlternatingT e m) where
    pure = Result
    (<*>) = ap

instance Monad m => MonadPlus (AlternatingT e m) where
    mzero = NoChoice
    mplus = AngelicChoice
    
instance (Applicative m, Monad m) => Alternative (AlternatingT e m) where
    empty = mzero
    (<|>) = mplus
    
instance Monad m => MonadOrElse (AlternatingT e m) where
    orElse c1 c2 = OrElse c1 c2 return

instance Monad m => MonadCut (AlternatingT e m) where
    cut = Cut
    
instance MonadTrans (AlternatingT e) where
    lift = Lazy . liftM return

instance MonadHoist (AlternatingT e) where
    hoist _ NoChoice = NoChoice
    hoist _ (Result r) = Result r
    hoist f (Lazy k) = Lazy (liftM (hoist f) (f k)) 
    hoist f (AngelicChoice x y) = AngelicChoice (hoist f x) (hoist f y)
    hoist f (DemonicChoice x y) = DemonicChoice (hoist f x) (hoist f y)
    hoist f (OrElse x y z) = OrElse (hoist f x) (hoist f y) (hoist f . z)
    hoist f (Cut x) = Cut (hoist f x)
    hoist f Success = Success
    hoist f (Failure e) = Failure e
    hoist f (Retry x h) = Retry (hoist f x) (fmap (fmap (hoist f)) h)

instance MonadIO m => MonadIO (AlternatingT e m) where
    liftIO = lift . liftIO
    
instance MonadReader r m => MonadReader r (AlternatingT e m) where
    ask = lift ask
    local m = hoist (local m)

    
instance Monad m => MonadDemonic (AlternatingT e m) where
    (<#>) = DemonicChoice
    succeed = Success
    
runAlternatingT' :: Monad m => AlternatingT e m a -> ([e] -> m (Either [e] [a])) -> m (Either [e] [a])
runAlternatingT' NoChoice bt = bt []
runAlternatingT' (Result a) _ = return $ Right [a]
runAlternatingT' (Lazy k) bt = do
                            a <- k
                            runAlternatingT' a bt 
runAlternatingT' (AngelicChoice x y) bt = runAlternatingT' x (\e -> runAlternatingT' y (\e' -> bt (e <|> e')))
runAlternatingT' (DemonicChoice x y) bt = do
                            r0 <- runAlternatingT' x (return . Left)
                            case r0 of
                                Left e -> bt e
                                Right rs -> do
                                    r1 <- runAlternatingT' y (return . Left)
                                    case r1 of
                                        Left e -> bt e
                                        Right rs' -> return (Right (rs ++ rs'))
runAlternatingT' (OrElse x y z) bt = do
                        r0 <- runAlternatingT' x (return . Left)
                        case r0 of
                            Left e -> runAlternatingT' (y >>= z) bt
                            Right rs -> do
                                r1 <- foo [runAlternatingT' (z b) (return . Left) | b <- rs] []
                                case r1 of
                                    Left e -> bt e
                                    rs' -> return rs'  
        where
            foo [] rs = return (Right rs)
            foo (a:aa) rs = do
                r0 <- a
                case r0 of
                    Left e -> return (Left e)
                    Right rs' -> foo aa (rs ++ rs')  
runAlternatingT' (Cut x) bt = runAlternatingT' x (return . Left)
runAlternatingT' Success bt = return (Right [])
runAlternatingT' (Failure e) bt = bt [e]
runAlternatingT' (Retry x h) bt = runAlternatingT' x bt'
        where
            bt' es = runAlternatingT' (msum [maybe (Failure e) id (h e) | e <- es]) bt

runAlternatingT :: Monad m => AlternatingT e m a -> m (Maybe [a])
runAlternatingT a = liftM (either (const Nothing) Just) $ runAlternatingT' a (return . Left)
