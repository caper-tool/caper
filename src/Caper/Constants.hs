-- |This module defines constants that determine aspects of Caper's
-- behaviour.  In future, these may be user-configurable and with some
-- degree of granularity.
module Caper.Constants(
    stabiliseBeforeConsumeInvariant,
    stabiliseBeforeConsumePostcondition,
    stabiliseBeforeConsumePrecondition,
    stabiliseAfterProduceInvariant,
    stabiliseAfterProducePostcondition,
    stabiliseAfterProducePrecondition,
    returnVariableName,
    defaultPreconditionBool,
    defaultPostconditionBool,
    programVariableSupersedesLogicalVariable,
    defaultRegionConstructionLimit,
    defaultRegionOpenLimit,
    closureDepth
)
 where

{- |Base configuration choice for stabilising before consuming assertions.

    If this is 'True', assertions are stabilised before they are consumed.
    This means they have a /weakest stable stronger assertion/ flavour.
    
    It should generally not be that both 'stabiliseBeforeConsume' and
    'stabiliseAfterProduce' are both 'True', since this means assertions
    will effectively be stabilised twice.  This has an effect on unstable
    (or at least not-provably-stable) assertions, although stable assertions
    would not be affected.  It would also mean performing more (unnecessary)
    stabilisation computation.
-} 
stabiliseBeforeConsume :: Bool
stabiliseBeforeConsume = True

{- |Base configuration choice for stabilising after producing assertions.

    If this is 'True', assertions are stabilised after they are produced.
    This means they have a /strongest stable weaker assertion/ flavour.
-}
stabiliseAfterProduce :: Bool
stabiliseAfterProduce = not stabiliseBeforeConsume

stabiliseBeforeConsumePrecondition :: Bool
stabiliseBeforeConsumePrecondition = stabiliseBeforeConsume

stabiliseAfterProducePrecondition :: Bool
stabiliseAfterProducePrecondition = stabiliseAfterProduce

stabiliseBeforeConsumePostcondition :: Bool
stabiliseBeforeConsumePostcondition = stabiliseBeforeConsume

stabiliseAfterProducePostcondition :: Bool
stabiliseAfterProducePostcondition = stabiliseAfterProduce

stabiliseBeforeConsumeInvariant :: Bool
stabiliseBeforeConsumeInvariant = stabiliseBeforeConsume

stabiliseAfterProduceInvariant :: Bool
stabiliseAfterProduceInvariant = stabiliseAfterProduce

-- |This name is a reserved logical variable in a postcondition that
-- refers to the value returned by the function.
returnVariableName :: String
returnVariableName = "ret"

-- |This determines whether the default precondition for a procedure
-- (when not otherwise specified) is True or False.
defaultPreconditionBool :: Bool
defaultPreconditionBool = False

-- |This determines whether the default postcondition for a procedure
-- (when not otherwise specified) is True or False.
defaultPostconditionBool :: Bool
defaultPostconditionBool = False

-- |This determines if a logical variable is superseded by a program
-- variable of the same name when consuming an invariant or assertion
programVariableSupersedesLogicalVariable :: Bool
programVariableSupersedesLogicalVariable = True

-- |This limits how many regions may be constructed in consuming an
-- assertion.  Setting this too high may slow down failing proof
-- searches without benefit.
defaultRegionConstructionLimit :: Int
defaultRegionConstructionLimit = 2

-- |This limits how many regions may be opened when performing an
-- atomic operation.  Setting this too high may slow down failing
-- proof searches without benefit.  Setting it too low may of course
-- cause some proof searches that should succeed to fail.
defaultRegionOpenLimit :: Int
defaultRegionOpenLimit = 2

-- |This determines the number of times to iterate the transitive
-- closure process for non-finite-state regions.  A setting of 0
-- will not check transitivity (if there are any actions).  A
-- setting of one will check transitivity, but not add any actions.
-- A higher setting will add transitions (of length up to 2^(n-1))
-- if doing so reaches a transitively closed set of actions.
closureDepth :: Int
closureDepth = 5
