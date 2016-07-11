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
import Control.Lens hiding (Lazy)
import Data.List
import Data.Maybe
import System.IO

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
    Label :: String -> AlternatingT e m a -> AlternatingT e m a

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
    fmap f (Label s x) = Label s (fmap f x)
    
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
            Label s x -> Label s (x >>= b)
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
    hoist f (Label s x) = Label s (hoist f x)

instance MonadIO m => MonadIO (AlternatingT e m) where
    liftIO = lift . liftIO
    
instance MonadReader r m => MonadReader r (AlternatingT e m) where
    ask = lift ask
    local m = hoist (local m)
    
instance Monad m => MonadDemonic (AlternatingT e m) where
    (<#>) = DemonicChoice
    succeed = Success

instance Monad m => MonadLabel (AlternatingT e m) where
    label l = Label l (Result ())
    
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
runAlternatingT' (Label s a) bt = runAlternatingT' a bt

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
runAlternatingTD' (Label l x) bt s = mps ("! " ++ l) >> runAlternatingTD' x bt s

runAlternatingTD :: (Monad m, MonadIO m, Show e) => AlternatingT e m a -> m (Maybe [a])
runAlternatingTD a = liftM (either (const Nothing) (Just . map snd)) $ runAlternatingTD' a (return . Left) ""

runAlternatingTD2 :: (Monad m, MonadIO m, Show e) => AlternatingT e m () -> m Bool
runAlternatingTD2 = liftM isJust . runAlternatingTD 


data AltTree e m = ATAng [(String, AltTree e m)] | ATDem [(String, AltTree e m)] | ATLab String (AltTree e m) | ATWork (AlternatingT e m ())

data AltCtx e m = ACTop
    | ACAng (AltCtx e m) [(String, AltTree e m)] String [(String, AltTree e m)]
    | ACDem (AltCtx e m) [(String, AltTree e m)] String [(String, AltTree e m)]
    | ACLab (AltCtx e m) String

printContext :: (Monad m, MonadIO m) => AltCtx e m' -> m ()
printContext ACTop = return ()
printContext (ACAng up _ l _) = printContext up >> mps ("A: " ++ l)
printContext (ACDem up _ l _) = printContext up >> mps ("D: " ++ l)
printContext (ACLab up l) = printContext up >> mps ("   " ++ l)

propagateSuccess :: AltCtx e m -> (AltCtx e m, AltTree e m)
propagateSuccess ACTop = (ACTop, ATWork Success)
propagateSuccess (ACAng up _ _ _) = propagateSuccess up
propagateSuccess (ACDem up x _ y) = (up, ATDem (x ++ y))
propagateSuccess (ACLab up _) = propagateSuccess up

propagateFailure :: AltCtx e m -> (AltCtx e m, AltTree e m)
propagateFailure ACTop = (ACTop, ATWork NoChoice)
propagateFailure (ACAng up x _ y) = (up, ATAng (x ++ y))
propagateFailure (ACDem up _ _ _) = propagateFailure up
propagateFailure (ACLab up _) = propagateFailure up

moveUp :: AltCtx e m -> AltTree e m -> (AltCtx e m, AltTree e m)
moveUp ACTop t = (ACTop, t)
moveUp (ACAng up lft l rgt) t = (up, ATAng (lft ++ (l, t) : rgt))
moveUp (ACDem up lft l rgt) t = (up, ATDem (lft ++ (l, t) : rgt))
moveUp (ACLab up l) t = moveUp up (ATLab l t)

intera :: (Monad m, MonadIO m, Show e) => AltCtx e m -> AltTree e m -> m Bool
intera ACTop (ATWork NoChoice) = return False -- Failed
intera ctx (ATWork NoChoice) = uncurry intera $ propagateFailure ctx
intera ACTop (ATWork (Result ())) = return True
intera ctx (ATWork (Result ())) = uncurry intera $ propagateSuccess ctx
intera ACTop (ATWork (Failure _)) = return False -- Failed
intera ctx (ATWork (Failure _)) = uncurry intera $ propagateFailure ctx
intera ACTop (ATWork Success) = return True
intera ctx (ATWork Success) = uncurry intera $ propagateSuccess ctx
intera ctx (ATWork (Lazy x)) = x >>= (intera ctx . ATWork)
intera ctx (ATWork acs@(AngelicChoice _ _)) = do
                acs' <- runLazyAngelic acs
                intera ctx (ATAng acs')
intera ctx (ATWork dcs@(DemonicChoice _ _)) = do
                dcs' <- runLazyDemonic dcs
                intera ctx (ATDem dcs')
intera ctx (ATWork acs@(OrElse _ _ _)) = do
                acs' <- runLazyAngelic acs
                intera ctx (ATAng acs')
intera ctx (ATWork (Cut x)) = intera ctx (ATWork x)
intera ctx (ATWork (Retry x _)) = intera ctx (ATWork x)
intera ctx (ATWork (LocalRetry c x _)) = intera ctx (ATWork (x >>= c))
intera ctx (ATWork (Label l c)) = intera (ACLab ctx l) (ATWork c)
intera ctx (ATLab l t) = intera (ACLab ctx l) t
intera ctx (ATAng []) = do
                    printContext ctx
                    mps "Failure"
                    uncurry intera $ propagateFailure ctx
intera ctx (ATAng [(l,a)]) = intera (ACLab ctx l) a
intera ctx t@(ATAng cs) = do
                    printContext ctx
                    mps "Angelic choices:"
                    opts <- iforM cs $ \i (a,ta) -> do
                                mps (show i ++ ". " ++ a)
                                let (top,_:rst) = splitAt i cs
                                return (show i, intera (ACAng ctx top a rst) ta)
                    makeChoice $ ("quit", return False) : ("up", uncurry intera $ moveUp ctx t) : opts
intera ctx (ATDem []) = do
                    printContext ctx
                    mps "Success"
                    uncurry intera $ propagateSuccess ctx
intera ctx (ATDem [(l,d)]) = intera (ACLab ctx l) d
intera ctx t@(ATDem cs) = do
                    printContext ctx
                    mps "Demonic choices:"
                    opts <- iforM cs $ \i (a,ta) -> do
                                mps (show i ++ ". " ++ a)
                                let (top,_:rst) = splitAt i cs
                                return (show i, intera (ACDem ctx top a rst) ta)
                    makeChoice $ ("quit", return False) : ("up", uncurry intera $ moveUp ctx t) : opts


makeChoice :: (Monad m, MonadIO m) => [(String, m a)] -> m a
makeChoice opts = do
            x <- liftIO $ do
                putStr "> "
                hFlush stdout
                getLine
            case find (\y -> x == fst y) opts of
                Nothing -> do
                    mps $ "Invalid choice.  Options are: " ++ intercalate "," (map fst opts)
                    makeChoice opts
                Just (_, a) -> a



showAltT :: (Monad m, Show e) => AlternatingT e m () -> String
showAltT (NoChoice) = "[Failure]"
showAltT (Failure e) = "[Failure: " ++ show e ++ "]"
showAltT (Result ()) = "[Success]"
showAltT (Success) = "[Success]"
showAltT (Lazy _) = "[Delayed]"
showAltT (AngelicChoice _ _) = "[Angleic Choice]"
showAltT (DemonicChoice _ _) = "[Demonic Choice]"
showAltT (OrElse _ _ _) = "[Angelic Choice (or else)]"
showAltT (Cut x) = showAltT x
showAltT (Retry x _) = showAltT x
showAltT (LocalRetry y x _) = showAltT (x >>= y)
showAltT (Label l _) = l


interactAlternatingT :: (Monad m, MonadIO m, Show e) => AlternatingT e m () -> m Bool
interactAlternatingT = intera ACTop . ATWork

runLazyAngelic :: (Monad m, Show e) => AlternatingT e m () -> m [(String, AltTree e m)]
runLazyAngelic NoChoice = return []
runLazyAngelic (Failure _) = return [] -- TODO: Change to handle failure handling
runLazyAngelic (Lazy k) = k >>= runLazyAngelic
runLazyAngelic (AngelicChoice x y) = do
                x' <- runLazyAngelic x
                y' <- runLazyAngelic y
                return $ x' ++ y'
runLazyAngelic (Cut x) = runLazyAngelic x
runLazyAngelic (OrElse x y z) = do
                x' <- runLazyAngelic (x >>= z)
                y' <- runLazyAngelic (y >>= z)
                return $ x' ++ y'
-- TODO: Don't ignore retries
runLazyAngelic (Retry x h) = runLazyAngelic x
runLazyAngelic (LocalRetry c x h) = runLazyAngelic (x >>= c)
runLazyAngelic (Label l x) = return [(l, ATWork x)]
runLazyAngelic o = return [(showAltT o, ATWork o)]

runLazyDemonic :: (Monad m, Show e) => AlternatingT e m () -> m [(String, AltTree e m)]
runLazyDemonic Success = return []
runLazyDemonic (Result ()) = return []
runLazyDemonic (Lazy k) = k >>= runLazyDemonic
runLazyDemonic (DemonicChoice x y) = do
                x' <- runLazyDemonic x
                y' <- runLazyDemonic y
                return $ x' ++ y'
runLazyDemonic (Cut x) = runLazyDemonic x
runLazyDemonic (Retry x h) = runLazyDemonic x
runLazyDemonic (LocalRetry c x h) = runLazyDemonic (x >>= c)
runLazyDemonic (Label l x) = return [(l, ATWork x)]
runLazyDemonic o = return [(showAltT o, ATWork o)]
