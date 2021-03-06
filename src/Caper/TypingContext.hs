{-# LANGUAGE FlexibleContexts, DeriveDataTypeable, MultiParamTypeClasses #-}
module Caper.TypingContext where
import Prelude hiding (foldl, foldr, mapM_)
import qualified Data.Map as Map
import Data.Foldable
import Data.Map (Map)
import qualified Data.Set as Set
import Control.Monad.State hiding (mapM_)
import Control.Monad.Exception
import Data.List hiding (foldl, foldr)
-- -- import Data.Monoid
import Data.Typeable

data TypeUnificationException v t = TypeUnificationException v t t
        | TypeUnificationException2 v t v t
        deriving (Typeable,Eq)

instance (Show v, Show t) => Show (TypeUnificationException v t) where
        show (TypeUnificationException v t tt) =
                "The variable '" ++ show v ++
                "' cannot be both " ++ show t ++ 
                " and " ++ show tt ++ "."
        show (TypeUnificationException2 v1 t1 v2 t2) =
                "The variables '" ++ show v1 ++
                "' (of type " ++ show t1 ++
                ") and '" ++ show v2 ++
                "' (of type " ++ show t2 ++
                ") are required to have the same type."

instance (Show v, Show t, Typeable v, Typeable t) =>
        Exception (TypeUnificationException v t)


newtype TContext v t = TContext (Map v (Either Int t), Int)

instance (Show v, Show t) => Show (TContext v t) where
        show (TContext (m, _)) = mconcat $ intersperse "," $ Map.foldWithKey (\v t -> ((show v ++ ":" ++ showType t) :)) [] m
                where
                        showType (Left i) = "?" ++ show i
                        showType (Right t) = show t

empty :: TContext v t
empty = TContext (Map.empty, 0)

data TypeResult t = JustType t | Undetermined | NotBound deriving (Eq, Ord)

lookup :: Ord v => v -> TContext v t -> TypeResult t
-- ^Determine the type of a variable in the context
lookup x (TContext (m, _)) = case Map.lookup x m of
                        Nothing -> NotBound
                        (Just (Left _)) -> Undetermined
                        (Just (Right t)) -> JustType t

bind :: (Ord v, Eq t, Failure (TypeUnificationException v t) m) =>
        v -> t -> TContext v t -> m (TContext v t)
-- ^Bind the type of a variable in the context
bind x t tc@(TContext (m, n)) = case Map.lookup x m of
                        Nothing -> return $ TContext (Map.insert x (Right t) m, n)
                        (Just a@(Left _)) -> return $ TContext (Map.map (\tt -> if tt == a then Right t else tt) m, n)
                        (Just (Right tt)) -> if t == tt then return tc else
                                failure (TypeUnificationException x t tt)

bindAll :: (Ord v, Eq t, Foldable f, Failure (TypeUnificationException v t) m) =>
        f v -> t -> TContext v t -> m (TContext v t)
bindAll vs t = execStateT $ 
                mapM_ (\v -> get >>= lift . bind v t >>= put) vs

declare :: (Ord v) => v -> TContext v t -> TContext v t
-- ^Declare a variable to be bound in the context
declare x tc@(TContext (m, n)) = if Map.member x m then tc else TContext (Map.insert x (Left n) m, n+1)

declareAll :: (Ord v, Foldable f) => f v -> TContext v t -> TContext v t
declareAll vs c = foldr declare c vs

unify :: (Ord v, Eq t, Failure (TypeUnificationException v t) m) =>
        v -> v -> TContext v t -> m (TContext v t)
-- ^Unify the types of two variables
unify v1 v2 tc@(TContext (m, n)) = case (Map.lookup v1 m, Map.lookup v2 m) of
                (Nothing, Nothing) -> return $ TContext (Map.insert v1 (Left n) $ Map.insert v2 (Left n) m, n+1)
                (Nothing, Just t) -> return $ TContext (Map.insert v1 t m, n)
                (Just t, Nothing) -> return $ TContext (Map.insert v2 t m, n)
                (Just a@(Left _), Just b) -> return $ TContext (Map.map (\tt -> if tt == a then b else tt) m, n)
                (Just a@(Right _), Just b@(Left _)) -> return $ TContext (Map.map (\tt -> if tt == b then a else tt) m, n)
                (Just (Right t1), Just (Right t2)) -> if t1 == t2 then return tc else failure (TypeUnificationException2 v1 t1 v2 t2)

toMap :: TContext v t -> Map v (Maybe t)
toMap (TContext (m, _)) = Map.map eitherToMaybe m
        where
                eitherToMaybe (Left _) = Nothing
                eitherToMaybe (Right t) = Just t

firstFresh :: (Ord v) => [v] -> TContext v t -> v
-- ^Returns the first element of the list that is fresh
firstFresh [] _ = error "firstFresh unable to find a fresh variable"
firstFresh (v:vs) tc@(TContext (m,_)) = if v `Map.member` m then firstFresh vs tc else v

difference :: (Ord v) => TContext v t -> TContext v t -> TContext v t
difference (TContext (m1, i1)) (TContext (m2, _)) = TContext (Map.difference m1 m2, i1)

intersection :: (Ord v) => TContext v t -> TContext v t -> TContext v t
-- ^Returns the first typing context restricted to the keys of the second.
intersection (TContext (m1, i1)) (TContext (m2, _)) = TContext (Map.intersection m1 m2, i1)

filter :: (v -> Bool) -> TContext v t -> TContext v t
filter f (TContext (m, i)) = TContext (Map.filterWithKey (\a b -> f a) m, i)

domain :: (Ord v) => TContext v t -> Set.Set v
domain (TContext (m, _)) = Set.fromAscList $ map fst $ Map.toAscList m
