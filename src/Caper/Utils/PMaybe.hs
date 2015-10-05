{-# LANGUAGE DeriveDataTypeable #-}
module Caper.Utils.PMaybe where
import           Control.Applicative
import           Control.Concurrent
import qualified Control.Concurrent.MSemN as Sem
import           Control.Exception
import           Control.Monad
import           Control.Monad.Trans.Maybe
import           Data.Typeable

newtype PMaybe a = PMaybe {
                runPMaybe :: Sem.MSemN Int -> MaybeT IO a
        }

data ResultUnneededException = ResultUnneededException deriving (Show, Typeable)
instance Exception ResultUnneededException

doRunPMaybe :: PMaybe a -> IO (Maybe a)
doRunPMaybe pm = do
        threads <- getNumCapabilities
        s <- Sem.new (threads - 1)
        runMaybeT $ runPMaybe pm s

instance Functor PMaybe where
        fmap f c = PMaybe $ fmap f . runPMaybe c

instance Applicative PMaybe where
        pure a = PMaybe $ \_ -> return a
        pf <*> pa = PMaybe $ \s -> runPMaybe pf s <*> runPMaybe pa s

instance Monad PMaybe where
        fail m = PMaybe $ \_ -> fail m
        c >>= f = PMaybe $ \s -> do
                                r1 <- runPMaybe c s
                                runPMaybe (f r1) s
        return = pure

instance Alternative PMaybe where
         empty = mzero
         (<|>) = mplus

instance MonadPlus PMaybe where
        mzero = fail ""
        c1 `mplus` c2 = PMaybe $ \s -> MaybeT $ mask $ \restore -> do
                (_, b) <- Sem.waitF s get1
                if b then do
                        relmv <- newEmptyMVar
                        let release = do
                                successful <- tryPutMVar relmv ()
                                when successful $ Sem.signal s 1
                        answermv <- newEmptyMVar
                        child1 <- forkIO $ child c1 answermv s
                        child2 <- forkIO $ child c2 answermv s
                        restore (do
                                res <- takeMVar answermv
                                release
                                case res of
                                        Nothing -> takeMVar answermv
                                        _ -> return res)
                                `finally` (do
                                        release
                                        forkIO (do
                                                throwTo child1 ResultUnneededException
                                                throwTo child2 ResultUnneededException))
                    else
                        restore $ runMaybeT $ runPMaybe c1 s `mplus` runPMaybe c2 s
            where
                get1 0 = (0, False)
                get1 _ = (1, True)
                child c mv sem = (do
                        res <- runMaybeT $! runPMaybe c sem
                        res' <- evaluate (evalMaybe res)
                        putMVar mv res') `catch` (\ResultUnneededException -> return ())
                evalMaybe (Just x) = x `seq` Just x
                evalMaybe Nothing = Nothing
