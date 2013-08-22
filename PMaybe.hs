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

newtype PMaybe a = PMaybe {
                runPMaybe :: Sem.MSemN Int -> MaybeT IO a
        }

data ResultUnneededException = ResultUnneededException Bool deriving (Show, Typeable)
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
                        tlog "+Acquired semaphore"
                        donemv <- newEmptyMVar
                        let release = do
                                tt <- tryPutMVar donemv ()
                                if tt then tlog "-Releasing semaphore" >> Sem.signal s 1 else return ()
                        childmv <- newEmptyMVar
                        childdonemv <- newEmptyMVar
                        pTId <- myThreadId
                        cTId <- forkIO (child pTId childmv s release childdonemv)
                        tlog $ "Started child: " ++ show cTId
                        result <- (restore $ ((runMaybeT $ runPMaybe c1 s) >>= evaluate . evalMaybe)) `catch`
                                (\ ex@(ResultUnneededException b) -> if b then do
                                                throwTo cTId ex
                                                tlog "Propagated exception"
                                                release
                                                throw ex
                                        else do
                                                tlog "Using child value"
                                                return Nothing)
 --                       tlog "Releasing semaphore"
                        release
                        case result of
                                Nothing -> do
                                        restore (do
                                                tlog $ "Awaiting child " ++ (show cTId)
                                                takeMVar childdonemv
                                                return ()) `catch`
                                                    (\ ex@(ResultUnneededException b) -> tlog "Exception while waiting for child" >> if b then do
                                                                throwTo cTId ex
                                                                throw ex
                                                        else return ())
                                        tlog "Child done"
                                        takeMVar childmv
                                _ -> do
                                        tlog $ "Abort child: " ++ (show cTId)
                                        restore (do
                                                throwTo cTId (ResultUnneededException True)
                                                tlog "Checking done"
                                                takeMVar childdonemv
                                                tlog "Child finished")
                                                `catch`
                                                (\ ex@(ResultUnneededException b) -> tlog "Exception while aborting" >> if b then
                                                        throw ex
                                                        else return ())
                                        tlog $ "Child aborted: " ++ show cTId
                                        return result
                else
                        restore $ runMaybeT $ runPMaybe c1 s `mplus` runPMaybe c2 s
            where
                get1 0 = (0, False)
                get1 _ = (1, True)
                child parent mv sem release donemv = (do
                        tlog "Child started"
                        res <- runMaybeT $! runPMaybe c2 sem
                        res' <- evaluate (evalMaybe res)
                        tlog "Child result"
                        putMVar mv res'
                        tlog "Result put"
                        release
                        case res' of
                                Nothing -> return () --tlog "No child answer"
                                _ -> do
                                        tlog $ "Throwing to parent " ++ show parent
                                        throwTo parent (ResultUnneededException False)
                                        tlog "Thrown"
                        putMVar donemv ()
                        ) `catch`
                                (\(ResultUnneededException b) -> do
                                        bb <- tryPutMVar donemv ()
                                        tlog $ "Thread exiting by: " ++ show b ++ " and mvar did: " ++ show bb)
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
