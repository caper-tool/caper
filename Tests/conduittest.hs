import Data.Conduit
import Control.Monad.Trans.Class
import qualified Data.Conduit.List as CL

source :: Source IO Int
source = do
        lift (putStrLn "wrote 1" >> return 1) >>= yield
        yieldOr 2 (putStrLn "wrote 2")
        yieldOr 3 (putStrLn "wrote 3")

conduit :: Conduit Int IO String
conduit = CL.map show

--sink :: Sink String IO () -- consumes a stream of Strings, no result
--sink = CL.mapM_ putStrLn

sink :: Sink String IO ()
sink = CL.isolate 2 =$ CL.mapM_ putStrLn

main = source $$ conduit =$ sink
