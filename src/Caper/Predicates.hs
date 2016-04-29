{-# LANGUAGE TemplateHaskell #-}
module Caper.Predicates where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet
import Control.Lens
import Data.List
import Control.Monad.Reader

import Caper.Utils.SimilarStrings
import Caper.ProverDatatypes
import Caper.Exceptions

-- |Predicate names are either 'String's or the special 
-- cases for heap cells: single cell or multiple (uninitialised) cells
data PredicateName = PName String | PCell | PCells deriving (Eq, Ord)
instance Show PredicateName where
        show (PName s) = s
        show PCell = "#cell"
        show PCells = "#cells"


data PredicateContext = PredicateContext {
        _predTypes :: Map PredicateName [VariableType]
        }
makeLenses ''PredicateContext

class PredicateLenses a where
        predicateContext :: Simple Lens a PredicateContext
        predicateTypes :: Simple Lens a (Map PredicateName [VariableType])
        predicateTypes = predicateContext . predicateTypes

instance PredicateLenses PredicateContext where
        predicateContext = id

-- |A (default) map from predicate names to the list of
-- types of the predicate parameters.  Here, we'll just
-- have a mapping for 'PCell' and 'PCells'
defaultPredicateTypes :: Map PredicateName [VariableType]
defaultPredicateTypes = Map.fromList [(PCell, [VTValue, VTValue]), -- A #cell has two value parameters
                        (PCells, [VTValue, VTValue])    -- A #cells has two value parameters (start and length)
                        ]

createPredicateContext :: Map String [(Maybe String, VariableType)] -> PredicateContext
createPredicateContext = PredicateContext . ifoldr (\pname pargs -> Map.insert (PName pname) (map snd pargs)) defaultPredicateTypes

-- |PVarBindings map program variables (modelled a 'String's) to
-- expressions
type PVarBindings = Map String (ValueExpression VariableID)

-- |LVarBindings map syntactic logical variables ('String's) to their internal
-- representations ('VariableID's)
type LVarBindings = Map String VariableID

emptyLVars :: LVarBindings
emptyLVars = Map.empty

-- |Predicates are maps from predicate names to multisets of
-- lists of parameters.  That is, for each predicate name
-- there's a bag of the parameters that we have copies of the
-- predicate for.  (Possibly want to use a list or something else
-- instead of 'MultiSet'?)
type Predicates = Map PredicateName (MultiSet [Expr VariableID])

predicateLookup :: PredicateName -> Predicates -> MultiSet [Expr VariableID]
predicateLookup = Map.findWithDefault MultiSet.empty

type Predicate = (PredicateName, [Expr VariableID])

toPredicateList :: Predicates -> [Predicate]
toPredicateList = Map.foldWithKey (\key val rest -> map ((,) key) (MultiSet.toList val) ++ rest) []

showPredicate :: Predicate -> String
showPredicate (PCell, [x, y]) = show x ++ " |-> " ++ show y
showPredicate (PCells, [x, y]) = show x ++ " |-> #cells(" ++ show y ++ ")"
showPredicate (PName s, l) = show s ++ "(" ++ intercalate "," (map show l) ++ ")"
showPredicate _ = error "showPredicate: Ill-formed predicate"

-- |Look up the type of a predicate.  Throw an exception if there is no predicate
-- of the given name in the context.
resolvePredicateType :: (MonadRaise m, MonadReader r m, PredicateLenses r) =>
        PredicateName -> m [VariableType]
resolvePredicateType pname = do
        pts <- view predicateTypes
        case pts ^. at pname of
                Nothing -> raise $ UndeclaredPredicate (show pname) (similarStrings (show pname) (map show $ Map.keys pts))
                Just vts -> return vts
