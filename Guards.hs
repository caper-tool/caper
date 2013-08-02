{-# LANGUAGE RankNTypes, MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable, FlexibleContexts #-}
{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE ScopedTypeVariables #-}
import Prelude hiding (catch,mapM,sequence,foldl,mapM_)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Control.Monad.Exception
import SaneProver
import Data.Foldable
import Data.Traversable

data PermissionExpression v =
                FullPerm
                | VarPerm v
                | PlusPerm (PermissionExpression v) (PermissionExpression v)
                deriving (Eq,Ord,Show,Functor,Foldable,Traversable)

type ValueExpression = ()

-- The empty guard type (ZeroGT) should not be allowed as a 
-- parameter to a sum or product.  We therefore split guard
-- types into two levels.

data TopLevelGuardTypeAST =
                ZeroGT | SomeGT GuardTypeAST

data GuardTypeAST =
                NamedGT String
                | NamedPermissionGT String
--                | ParametrisedGT String
                | ProductGT GuardTypeAST GuardTypeAST
                | SumGT GuardTypeAST GuardTypeAST
                deriving (Show)

data GuardTypeException =
                GTEMultipleOccurrence String (Maybe GuardTypeAST)
                deriving Typeable

instance Show GuardTypeException where
        show (GTEMultipleOccurrence s Nothing) = "Multiple guards named \"" ++ s ++ "\" are declared in a guard type."
        show (GTEMultipleOccurrence s (Just gt)) = "Multiple guards named \"" ++ s ++ "\" are declared in the guard type \"" ++ (show gt) ++ "\"."

instance Exception GuardTypeException


data GuardParameterType =
                UniqueGPT
                | PermissionGPT
--                | ValueGPT
                deriving (Eq,Ord,Show)

-- INVARIANT : instances of WeakGuardType must be non-empty
type WeakGuardType = Set.Set (Map.Map String GuardParameterType)

validateGuardTypeAST :: (Throws GuardTypeException l) => TopLevelGuardTypeAST -> EM l ()
validateGuardTypeAST ZeroGT = return ()
validateGuardTypeAST (SomeGT gt) = do
                        vgt Set.empty gt
                        return ()
        where
                vgt s (NamedGT n) = checkFresh s n
                vgt s (NamedPermissionGT n) = checkFresh s n
--                vgt s (ParametrisedGT n) = checkFresh s n
                vgt s (ProductGT gt1 gt2) = do
                                                s1 <- vgt s gt1
                                                vgt s1 gt2
                vgt s (SumGT gt1 gt2) = do
                                                s1 <- vgt s gt1
                                                vgt s1 gt2
                checkFresh s n = do if Set.member n s then throw $ GTEMultipleOccurrence n (Just gt) else return $ Set.insert n s

-- TODO: refactor these into somewhere more appropriate
mixWith :: (Ord a, Ord b, Ord c) => (a -> b -> c) -> Set.Set a -> Set.Set b -> Set.Set c
mixWith op s1 s2 = Set.unions $ Set.toList $ Set.map (\x -> Set.map (op x) s2) s1

listMixWith :: (a -> b -> c) -> [a] -> [b] -> [c]
listMixWith op l1 l2 = foldl (++) [] $ map (\x -> map (op x) l2) l1


toWeakGuardType :: GuardTypeAST -> WeakGuardType
toWeakGuardType (NamedGT n) = Set.singleton $ Map.singleton n UniqueGPT
toWeakGuardType (NamedPermissionGT n) = Set.singleton $ Map.singleton n PermissionGPT
--toWeakGuardType (ParametrisedGT n) = Set.singleton $ Map.singleton n ValueGPT
toWeakGuardType (ProductGT gt1 gt2) = mixWith Map.union (toWeakGuardType gt1) (toWeakGuardType gt2)
toWeakGuardType (SumGT gt1 gt2) = Set.union (toWeakGuardType gt1) (toWeakGuardType gt2)

topLevelToWeakGuardType :: TopLevelGuardTypeAST -> WeakGuardType
topLevelToWeakGuardType ZeroGT = Set.singleton Map.empty
topLevelToWeakGuardType (SomeGT gt) = toWeakGuardType gt


-- toWeakGuardTypeWorker :: WeakGuardType -> GuardType

data GuardAST v =
                EmptyG
                | NamedG String
                | NamedPermissionG String (PermissionExpression v)
                | ParametrisedG String ValueExpression
                | CoParametrisedG String [ValueExpression]
                | StarG (GuardAST v) (GuardAST v)
                deriving (Show,Functor,Foldable,Traversable)




data GuardException v =
                GEInconsistentOccurrences String (GuardAST v)
                deriving Typeable

instance Show v => Show (GuardException v) where
        show (GEInconsistentOccurrences s g) = "The guard named \"" ++ s ++ "\" is used inconsistently in the guard expression \"" ++ (show g) ++ "\"."

instance (Typeable v, Show v) => Exception (GuardException v)

data GuardParameters v = NoGP | PermissionGP (PermissionExpression v)
 -- | Parameters [ValueExpression] | CoParameters [ValueExpression] [ValueExpression]
        deriving (Show,Eq,Ord,Functor,Foldable,Traversable)

type Guard v = Map.Map String (GuardParameters v)

toGuard :: (Typeable v, Show v, Throws (GuardException v) l) => GuardAST v -> EM l (Guard v)
toGuard gast = tg (Map.empty) gast
        where
                tg g (EmptyG) = return g
                tg g (NamedG n) = if n `Map.member` g then throw (GEInconsistentOccurrences n gast) else return $ Map.insert n NoGP g
                tg g (NamedPermissionG n pe) = case Map.lookup n g of
                                        (Nothing) -> return $ Map.insert n (PermissionGP pe) g
                                        (Just (PermissionGP pe0)) -> return $ Map.insert n (PermissionGP (PlusPerm pe0 pe)) g
                                        _ -> throw $ GEInconsistentOccurrences n gast
{--                tg g (ParametrisedG n v) = case Map.lookup n g of
                                        (Nothing) -> return $ Map.insert n (Parameters [v]) g
                                        (Just (Parameters vs)) -> return $ Map.insert n (Parameters (v : vs)) g
                                        (Just (CoParameters vs covs)) -> return $ Map.insert n (CoParameters (v : vs) covs) g
                                        _ -> throw $ GEInconsistentOccurrences n gast
                tg g (CoParametrisedG n vs) = case Map.lookup n g of
                                        (Nothing) -> return $ Map.insert n (CoParameters [] vs) g
                                        (Just (Parameters vs')) -> return $ Map.insert n (CoParameters vs' vs) g
                                        _ -> throw $ GEInconsistentOccurrences n gast --}
                tg g (StarG ge1 ge2) = do
                                                g' <- tg g ge1
                                                tg g' ge2

checkGuardAtType :: Guard v -> WeakGuardType -> Bool
checkGuardAtType g gt = Set.fold (\m b -> b || Map.foldWithKey (matchin m) True g) False gt
        where
                matchin m k p b = b && case Map.lookup k m of
                                Nothing -> False
                                (Just x) -> matchup p x
                matchup NoGP UniqueGPT = True
                matchup (PermissionGP _) PermissionGPT = True
--                matchup (Parameters _) ValueGPT = True
--                matchup (CoParameters _ _) ValueGPT = True
                matchup _ _ = False

gtToG :: GuardParameterType -> GuardParameters v
gtToG UniqueGPT = NoGP
gtToG PermissionGPT = PermissionGP FullPerm
--gtToG ValueGPT = CoParameters [] []

fullGuard :: WeakGuardType -> Guard v
fullGuard gt = Map.map gtToG (Set.findMin gt)

fullGuards :: WeakGuardType -> [Guard v]
fullGuards = Prelude.map (Map.map gtToG) . Set.toList 

guardEquivalences :: GuardTypeAST -> [(Guard v,Guard v)]
guardEquivalences (SumGT gt1 gt2) = guardEquivalences gt1 ++ guardEquivalences gt2 ++ listMixWith (,) (fullGuards $ toWeakGuardType gt1) (fullGuards $ toWeakGuardType gt2)
guardEquivalences (ProductGT gt1 gt2) = guardEquivalences gt1 ++ guardEquivalences gt2
guardEquivalences _ = []

guardPrimitiveEntailment :: Guard VariableID -> Guard EVariable -> Prover (Maybe (Guard VariableID))
-- Checks if first guard entails second without rewrites
-- Returns the frame if so, Nothing otherwise
guardPrimitiveEntailment g1 g2 = error "Not done!"
