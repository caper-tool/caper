{-# LANGUAGE TemplateHaskell #-}
module Caper.Contexts where

import Control.Lens
import Data.Map (Map)

import Caper.ProverDatatypes
import Caper.ExceptionContext
import Caper.RegionTypes
import Caper.Procedures
 
data ProcedureContext = ProcedureContext {
        _pcSpecificationContext :: Map String Specification,  
        _pcRegionTypeContext :: RegionTypeContext,
        _pcProverContext :: ProverRecord,
        _pcExceptionContext :: [ExceptionContext]
        }
makeLenses ''ProcedureContext

instance SpecificationContext ProcedureContext where
        specifications = pcSpecificationContext

instance Provers ProcedureContext where
        permissionsProver = permissionsProver . _pcProverContext
        valueProver = valueProver . _pcProverContext  

instance RTCGetter ProcedureContext where
        theRTContext = pcRegionTypeContext
        
instance ECLenses ProcedureContext where
        exceptionContext = pcExceptionContext