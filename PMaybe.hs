{-# LANGUAGE DeriveDataTypeable #-}
module PMaybe where
import Control.Exception
import Control.Concurrent
import Control.Concurrent.MVar
import qualified Control.Concurrent.MSemN as Sem
import Control.Monad.Trans.Maybe
import Data.Typeable
import Control.Monad
import Debug.Trace
import Prelude hiding (catch)

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

instance Monad PMaybe where
        fail m = PMaybe $ \_ -> fail m
        c >>= f = PMaybe $ \s -> do
                                r1 <- runPMaybe c s
                                runPMaybe (f r1) s
        return r = PMaybe $ \_ -> return r

instance MonadPlus PMaybe where
        mzero = fail ""
        c1 `mplus` c2 = PMaybe $ \s -> MaybeT $ mask $ \restore -> do
                (_, b) <- Sem.waitF s get1
                if b then do
                        relmv <- newEmptyMVar
                        let release = do
                                b <- tryPutMVar relmv ()
                                if b then Sem.signal s 1 else return ()
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
                                        forkIO $ (do
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
                tlog m = do
                        tid <- myThreadId
                        putStrLn $ show tid ++ "> " ++ m 

{-
foo n = return $ head $ filter (\x -> x `mod` n == 0) [1..]

main = do
        res <- doRunPMaybe (foo 1000111111 `mplus` foo 101010101)
        print res --(foo 100011111 `mplus` foo 101010101 :: Maybe Integer)
        -}
