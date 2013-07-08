{-# LANGUAGE RankNTypes, MultiParamTypeClasses, FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable, FlexibleContexts #-}
import Prelude hiding (catch)
import Data.Map as Map
import Data.Set as Set
import Control.Monad.Exception

data PermissionExpression =
                FullPerm
                | VarPerm String
                | EVarPerm String
                | PlusPerm PermissionExpression PermissionExpression


type ValueExpression = ()


data GuardTypeAST =
                ZeroGT
                | NamedGT String
                | NamedPermissionGT String
                | ParametrisedGT String
                | ProductGT GuardTypeAST GuardTypeAST
                | SumGT GuardTypeAST GuardTypeAST
                deriving (Show)

data GuardTypeException =
                GTEMultipleOccurrence String (Maybe GuardTypeAST)
                deriving Typeable

instance Show GuardTypeException where
        show (GTEMultipleOccurrence s Nothing) = "Multiple guards named \"" ++ s ++ "\" were declared in a guard type."
        show (GTEMultipleOccurrence s (Just gt)) = "Multiple guards named \"" ++ s ++ "\" were declared in the guard type \"" ++ (show gt) ++ "\"."

instance Exception GuardTypeException


data GuardParameterType =
                UniqueGPT | PermissionGPT | ValueGPT
                deriving (Eq,Ord,Show)

type WeakGuardType = Set.Set (Map.Map String GuardParameterType)

validateGuardTypeAST :: (Throws GuardTypeException l) => GuardTypeAST -> EM l ()
validateGuardTypeAST gt = do
                        vgt Set.empty gt
                        return ()
        where
                vgt s ZeroGT = return s
                vgt s (NamedGT n) = checkFresh s n
                vgt s (NamedPermissionGT n) = checkFresh s n
                vgt s (ParametrisedGT n) = checkFresh s n
                vgt s (ProductGT gt1 gt2) = do
                                                s1 <- vgt s gt1
                                                vgt s1 gt2
                vgt s (SumGT gt1 gt2) = do
                                                s1 <- vgt s gt1
                                                vgt s1 gt2
                checkFresh s n = do if Set.member n s then throw $ GTEMultipleOccurrence n (Just gt) else return $ Set.insert n s
                
mixWith :: (Ord a, Ord b, Ord c) => (a -> b -> c) -> Set.Set a -> Set.Set b -> Set.Set c
mixWith op s1 s2 = Set.unions $ Set.toList $ Set.map (\x -> Set.map (op x) s2) s1


toWeakGuardType :: GuardTypeAST -> WeakGuardType
toWeakGuardType ZeroGT = Set.singleton Map.empty
toWeakGuardType (NamedGT n) = Set.singleton $ Map.singleton n UniqueGPT
toWeakGuardType (NamedPermissionGT n) = Set.singleton $ Map.singleton n PermissionGPT
toWeakGuardType (ParametrisedGT n) = Set.singleton $ Map.singleton n ValueGPT
toWeakGuardType (ProductGT gt1 gt2) = mixWith Map.union (toWeakGuardType gt1) (toWeakGuardType gt2)
toWeakGuardType (SumGT gt1 gt2) = Set.union (toWeakGuardType gt1) (toWeakGuardType gt2)

-- toWeakGuardTypeWorker :: WeakGuardType -> GuardType

data GuardAST =
                EmptyG
                | NamedG String
                | NamedPermissionG String PermissionExpression
                | ParametrisedG String ValueExpression
                | CoParametrisedG String [ValueExpression]
                | StarG Guard Guard




data GuardParameters = NoGP | PermissionGP PermissionExpression | Parameters [ValueExpression] | CoParameters [ValueExpression] [ValueExpression]

data GuardType =
                GEInconsistentOccurrences String GuardAST
                deriving Typeable

instance Show GuardTypeException where
        show (GTEMultipleOccurrence s Nothing) = "Multiple guards named \"" ++ s ++ "\" were declared in a guard type."
        show (GTEMultipleOccurrence s (Just gt)) = "Multiple guards named \"" ++ s ++ "\" were declared in the guard type \"" ++ (show gt) ++ "\"."

instance Exception GuardTypeException

type Guard = Map.Map String GuardParameters

toGuard :: GuardAST -> Guard
