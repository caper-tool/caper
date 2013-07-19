{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
module Prover where


-- Should I use the State monad?
--import Control.Monad.State

class Prover context atom var | context -> atom var where
        emptyContext :: context
        -- Introduce a variable that is chosen by the environment
        demonicVar :: context -> (var, context)
        -- Introduce a variable that is chosen by the prover
        angelicVar :: context -> (var, context)
        -- Assert an atomic statement to be true
        assertTrue :: atom -> context -> context
        assertFalse :: atom -> context -> context
        -- Assume an atomic statement to be true
        assumeTrue :: atom -> context -> context
        assumeFalse :: atom -> context -> context

        -- The angel cannot force the last assertion to hold
        isInvalid :: context -> IO (Maybe Bool)
        -- The angel can force any subsequent assertion to hold
        isInconsistent :: context -> IO (Maybe Bool)

import Permissions

data PermissionContext = PC (DPF -> DPF) Int

type PermissionVar = Int

data PermissionAtom = PermEq PermissionVar PermissionVar
                | PermDis PermissionVar PermissionVar
                | PermComp PermissionVar PermissionVar PermissionVar

permAtomToDPF :: PermissionAtom -> Int -> DPF
permAtomToDPF (PermEq v1 v2) n = DEq (n - v1) (n - v2)
permAtomToDPF (PermDis v1 v2) n = DDis (n - v1) (n - v2)
permAtomToDPF (PermComp v1 v2 v3) n = DC (n - v1) (n - v2) (n - v3)

-- TODO: Fail faster on assertions/assumptions that use invalid variables

instance Prover PermissionContext PermissionAtom PermissionVar where
        emptyContext = PC id 0
        demonicVar (PC c n) = (n+1, PC (c . DAll) (n + 1))
        angelicVar (PC c n) = (n+1, PC (c . DEx) (n + 1))
        assumeTrue a (PC c n) = PC (c . (dImpl (permAtomToDPF a n))) n
        assumeFalse a (PC c n) = PC (c . (DOr (permAtomToDPF a n))) n
        assertTrue a (PC c n) = PC (c . (DAnd (permAtomToDPF a n))) n
        assertFalse a (PC c n) = PC (c . (DAnd $ DNot $ permAtomToDPF a n)) n
        isInvalid (PC c n) = return $ Just $ not $ dpf_eval $ c (DNot DFalse)
        isInconsistent (PC c n) = return $ Just $ dpf_eval $ c DFalse

