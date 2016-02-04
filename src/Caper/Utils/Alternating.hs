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
    LocalRetry :: (b -> AlternatingT e m a) -> AlternatingT e m b -> (e -> Maybe (AlternatingT e m b)) ->  AlternatingT e m a

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
    fmap f (LocalRetry c x h) = LocalRetry (fmap f . c) x h
    
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
            LocalRetry c x h -> LocalRetry (c >=> b) x h
    fail s = trace s NoChoice

instance Failure e (AlternatingT e m) where
    failure = Failure

instance (Monad m) => OnFailure e (AlternatingT e m) where
    retry = Retry
    localRetry = LocalRetry return
    
instance (Applicative m, Monad m) => Applicative (AlternatingT e m) where
    pure = Result
    (<*>) = ap

instance Monad m => MonadPlus (AlternatingT e m) where
    mzero = NoChoice
    mplus NoChoice x = x
    mplus x NoChoice = x
    mplus x y = AngelicChoice x y
    
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
    hoist f (LocalRetry c x h) = LocalRetry (hoist f . c) (hoist f x) (fmap (fmap (hoist f)) h)

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
runAlternatingT' (LocalRetry c x h) bt = do
            r0 <- runAlternatingT' x bt'
            case r0 of
                Left e -> bt e
                Right rs -> runAlternatingT' (msum (map return rs) >>= c) bt
        where
            bt' es = runAlternatingT' (msum [maybe (Failure e) id (h e) | e <- es]) (return . Left)

runAlternatingT :: Monad m => AlternatingT e m a -> m (Maybe [a])
runAlternatingT a = liftM (either (const Nothing) Just) $ runAlternatingT' a (return . Left)

mps :: MonadIO m => String -> m ()
mps = liftIO . putStrLn

runAlternatingTD' :: (Monad m, MonadIO m, Show e) => AlternatingT e m a -> ([e] -> m (Either [e] [(String, a)])) -> String -> m (Either [e] [(String, a)])
runAlternatingTD' NoChoice bt s = mps (s ++ "#") >> bt []
runAlternatingTD' (Result a) _ s = mps (s ++ "$") >> (return $ Right [(s ++ "$", a)])
runAlternatingTD' (Lazy k) bt s = do
                            a <- k
                            runAlternatingTD' a bt s 
runAlternatingTD' (AngelicChoice x y) bt s = mps (s ++ "A0.") >> runAlternatingTD' x (\e -> mps (s ++ "A1.") >> runAlternatingTD' y (\e' -> bt (e <|> e')) (s ++ "A1.")) (s ++ "A0.")
runAlternatingTD' (DemonicChoice x y) bt s = do
                            mps (s ++ "D0.")
                            r0 <- runAlternatingTD' x (return . Left) (s ++ "D0.")
                            case r0 of
                                Left e -> bt e
                                Right rs -> do
                                    mps (s ++ "D1.")
                                    r1 <- runAlternatingTD' y (return . Left) (s ++ "D1.")
                                    case r1 of
                                        Left e -> bt e
                                        Right rs' -> return (Right (rs ++ rs'))
runAlternatingTD' (OrElse x y z) bt s = do
                        mps (s ++ "O[")
                        r0 <- runAlternatingTD' x (return . Left) (s ++ "O[")
                        case r0 of
                            Left e -> mps (s ++ "OF.") >> runAlternatingTD' (y >>= z) bt (s ++ "OF.")
                            Right rs -> do
                                r1 <- foo [mps (s' ++ "].") >> runAlternatingTD' (z b) (return . Left) (s' ++ "].") | (s', b) <- rs] []
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
runAlternatingTD' (Cut x) bt s = mps (s ++ ".!.") >> runAlternatingTD' x (return . Left) (s ++ ".!.")
runAlternatingTD' Success bt s = mps (s ++ "$") >> return (Right [])
runAlternatingTD' (Failure e) bt s = mps (s ++ "#" ++ show e) >> bt [e]
runAlternatingTD' (Retry x h) bt s = mps (s ++ "R0.") >> runAlternatingTD' x bt' (s ++ "R0.")
        where
            bt' es = mps (s ++ "R1" ++ show es ++ ".") >> runAlternatingTD' (msum [maybe (Failure e) id (h e) | e <- es]) bt (s ++ "R1.")
runAlternatingTD' (LocalRetry c x h) bt s = do
            mps (s ++ "r0[")
            r0 <- runAlternatingTD' x bt' (s ++ "r0[")
            case r0 of
                Left e -> bt e
                Right rs -> runAlternatingTD' (msum (map (return . snd) rs) >>= c) bt (s ++ "r0[].")
        where
            bt' es = mps (s ++ "r1" ++ show es ++ ".") >>
                runAlternatingTD' (msum [maybe (Failure e) id (h e) | e <- es]) (return . Left) (s ++ "r1.")

runAlternatingTD :: (Monad m, MonadIO m, Show e) => AlternatingT e m a -> m (Maybe [a])
runAlternatingTD a = liftM (either (const Nothing) (Just . map snd)) $ runAlternatingTD' a (return . Left) ""
