module Caper.Utils.MemoIO where
import qualified Data.Map as Map
import Data.IORef
import Control.Monad.IO.Class

memoIO :: (Eq a, Ord a, MonadIO m) => (a -> m b) -> IO (a -> m b)
memoIO f = do
        cacheref <- newIORef Map.empty
        return $ \x -> do
                cache <- liftIO $ readIORef cacheref
                case Map.lookup x cache of
                        Nothing -> do
                                r <- f x
                                liftIO $ modifyIORef cacheref (Map.insert x r)
                                return r
                        (Just r) -> return r
