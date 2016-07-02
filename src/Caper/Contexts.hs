{-# LANGUAGE TemplateHaskell #-}
module Caper.Contexts where

import Control.Lens
import Data.Map (Map)

import Caper.Constants
import Caper.ProverDatatypes
import Caper.ExceptionContext
import Caper.RegionTypes
import Caper.Procedures
import Caper.Predicates

data ConfigurationContext = ConfigurationContext {
        ccRegionConstructionLimit :: Int,
        ccRegionOpenLimit :: Int
        }

class Configuration c where
        regionConstructionLimit :: c -> Int
        regionOpenLimit :: c -> Int

defaultConfiguration :: ConfigurationContext
defaultConfiguration = ConfigurationContext {
        ccRegionConstructionLimit = defaultRegionConstructionLimit,
        ccRegionOpenLimit = defaultRegionOpenLimit
        }

data ProcedureContext = ProcedureContext {
        _pcConfigurationContext :: ConfigurationContext,
        _pcSpecificationContext :: Map String Specification,  
        _pcRegionTypeContext :: RegionTypeContext,
        _pcPredicateContext :: PredicateContext,
        _pcProverContext :: ProverRecord,
        _pcExceptionContext :: [ExceptionContext]
        }
makeLenses ''ProcedureContext

instance Configuration ProcedureContext where
        regionConstructionLimit = ccRegionConstructionLimit . _pcConfigurationContext
        regionOpenLimit = ccRegionOpenLimit . _pcConfigurationContext

instance SpecificationContext ProcedureContext where
        specifications = pcSpecificationContext

instance Provers ProcedureContext where
        permissionsProver = permissionsProver . _pcProverContext
        valueProver = valueProver . _pcProverContext  

instance RTCGetter ProcedureContext where
        theRTContext = pcRegionTypeContext
        
instance ECLenses ProcedureContext where
        exceptionContext = pcExceptionContext

instance PredicateLenses ProcedureContext where
        predicateContext = pcPredicateContext

data ProverContext = ProverContext {
        _pvcProverContext :: ProverRecord,
        _pvcExceptionContext :: [ExceptionContext]
        }
makeLenses ''ProverContext

instance Provers ProverContext where
        permissionsProver = permissionsProver . _pvcProverContext
        valueProver = valueProver . _pvcProverContext

instance ECLenses ProverContext where
        exceptionContext = pvcExceptionContext

