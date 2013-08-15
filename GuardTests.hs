import Prelude hiding (catch,mapM,sequence,foldl,mapM_)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Exception
import Control.Monad hiding (mapM)
import Control.Monad.State hiding (mapM_,mapM)
import Control.Monad.Trans.Maybe
import ProverDatatypes
import PermissionsInterface
import Guards
import PermissionsE
import Permissions
import SaneProver

gt1 = ProductGT (NamedPermissionGT "A") (SumGT (NamedPermissionGT "B") (ProductGT (NamedGT "C") (NamedGT "D")))

gt2 = ProductGT (SumGT (NamedPermissionGT "A") (NamedPermissionGT "Z")) (SumGT (NamedPermissionGT "B") (ProductGT (NamedGT "C") (NamedGT "D")))


cont1 = snd $ runState x emptyContext
        where
                x = do
                        foo <- checkBindVariable () "foo" VTPermission
                        assertPermissionFalse $ PAEq (PEVar foo) (PEFull)
                        assertPermissionFalse $ PAEq (PEVar foo) (PEZero)
                        bar <- checkBindVariable () "bar" VTPermission
                        assertPermissionFalse $ PAEq (PEVar bar) (PEFull)
                        assertPermissionFalse $ PAEq (PEVar bar) (PEZero)

cont2 = execState x cont1
        where
                x = do
                        assertPermissionFalse $ PADis (PEVar $ VIDNamed () "foo") (PEVar $ VIDNamed () "bar")


gd1 = GD (Map.fromList [("A", NoGP), ("B", NoGP)])
gd2 = GD (Map.fromList [("B", NoGP)])
gd3 = GD (Map.fromList [("A", PermissionGP PEFull), ("B", PermissionGP (PEVar $ VIDNamed () "foo"))])
gd3a = fmap EVNormal gd3
gd4 = GD (Map.fromList [("A", PermissionGP $ PEVar $ VIDNamed () "bar")])
gd5a = GD (Map.fromList [("A", PermissionGP $ PEVar $ EVExistential () "zop")])
gd6a = GD (Map.fromList [("A", PermissionGP $ PEVar $ EVExistential () "zop"), ("B", PermissionGP $ PEVar $ EVExistential () "zop")])
gd7 = GD (Map.fromList [("A", PermissionGP $ PEVar $ VIDNamed () "bar"), ("B", PermissionGP (PEVar $ VIDNamed () "foo"))])

gd8 = GD (Map.fromList [("A", PermissionGP $ PEVar $ VIDNamed () "foo"), ("D", NoGP), ("C", NoGP)])

gtest :: (PermissionsProver p) => p -> Context -> Guard VariableID -> Guard EVariable -> IO (Maybe (Guard EVariable, Context))
gtest prover c g1 g2 = runMaybeT $ runStateT x c
        where
                x :: StateT Context (MaybeT IO) (Guard EVariable)
                x = do
                        r <- guardPrimitiveEntailment prover g1 g2 
                        return $ fst r

main :: IO ()
main = do
        epp <- makeEPProver
        r <- gtest epp cont2 gd7 gd6a
        putStrLn $ show r
