module Provers where
import ProverDatatypes
import PermissionsInterface
import Permissions
import PermissionsE
import ValueProver
import FirstOrder

getEZ3Provers :: IO Provers
getEZ3Provers = do
        epp <- makeEPProver
        let z3vp = valueCheck
        return $ Provers (permCheck epp . simplify) z3vp

getInternalZ3Provers :: IO Provers
getInternalZ3Provers =
        return $ Provers (permCheck (TPProver ()) . simplify . (rewriteFOF simplR)) valueCheck
