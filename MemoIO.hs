module MemoIO where
import qualified Data.Map as Map
import Data.Map (Map)
import Data.IORef

memoIO :: (Eq a, Ord a) => (a -> IO b) -> IO (a -> IO b)
memoIO f = do
        cacheref <- newIORef Map.empty
        return $ \x -> do
                cache <- readIORef cacheref
                case Map.lookup x cache of
                        Nothing -> do
                                r <- f x
                                modifyIORef cacheref (Map.insert x r)
                                return r
                        (Just r) -> return r
