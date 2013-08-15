module PermissionsInterface where
import ProverDatatypes
import Data.Maybe
import Control.Monad

class PermissionsProver p where
        -- Tries to determine whether the given first-order permission formula
        -- is true or false
        permCheck :: p -> FOF PermissionAtomic String -> IO (Maybe Bool)
        -- permCheckTrue behaves like permCheck but will return False if the
        -- outcome is indeterminate
        permCheckTrue :: p -> FOF PermissionAtomic String -> IO Bool
        permCheckTrue this f = liftM (fromMaybe False) (permCheck this f) 
