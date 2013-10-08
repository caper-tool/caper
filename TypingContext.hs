{-# LANGUAGE FlexibleContexts #-}
module TypingContext where
import Prelude hiding (foldl, foldr, mapM_)
import qualified Data.Map as Map
import Data.Foldable
import Data.Map (Map)
import Control.Monad.State hiding (mapM_)
import Exceptions

newtype TContext v t = TContext (Map v (Either Int t), Int)

empty :: TContext v t
empty = TContext (Map.empty, 0)

data TypeResult t = JustType t | Undetermined | NotBound deriving (Eq, Ord)

lookup :: Ord v => v -> TContext v t -> TypeResult t
-- Determine the type of a variable in the context
lookup x (TContext (m, _)) = case Map.lookup x m of
                        Nothing -> NotBound
                        (Just (Left _)) -> Undetermined
                        (Just (Right t)) -> JustType t

bind :: (Ord v, Show v, Show t, Typeable v, Typeable t, Eq t, Monad m, Throws (TypeUnificationException v t) l) =>
        v -> t -> TContext v t -> EMT l m (TContext v t)
-- Bind the type of a variable in the context
bind x t tc@(TContext (m, n)) = case Map.lookup x m of
                        Nothing -> return $ TContext (Map.insert x (Right t) m, n)
                        (Just a@(Left _)) -> return $ TContext (Map.map (\tt -> if tt == a then Right t else tt) m, n)
                        (Just (Right tt)) -> if t == tt then return tc else
                                throw (TypeUnificationException x t tt)

bindAll :: (Ord v, Show v, Typeable v, Monad m, Show t, Eq t, Typeable t, Foldable f, Throws (TypeUnificationException v t) l) =>
        f v -> t -> TContext v t -> EMT l m (TContext v t)
bindAll vs t = execStateT $ 
                mapM_ (\v -> get >>= lift . bind v t >>= put) vs

declare :: (Ord v) => v -> TContext v t -> TContext v t
-- Declare a variable to be bound in the context
declare x tc@(TContext (m, n)) = if Map.member x m then tc else TContext (Map.insert x (Left n) m, n+1)

declareAll :: (Ord v, Foldable f) => f v -> TContext v t -> TContext v t
declareAll vs c = foldr declare c vs

unify :: (Ord v, Eq t, Show v, Show t, Typeable v, Typeable t, Monad m, Throws (TypeUnificationException v t) l) =>
        v -> v -> TContext v t -> EMT l m (TContext v t)
-- Unify the types of two variables
unify v1 v2 tc@(TContext (m, n)) = case (Map.lookup v1 m, Map.lookup v2 m) of
                (Nothing, Nothing) -> return $ TContext (Map.insert v1 (Left n) $ Map.insert v2 (Left n) m, n+1)
                (Nothing, Just t) -> return $ TContext (Map.insert v1 t m, n)
                (Just t, Nothing) -> return $ TContext (Map.insert v2 t m, n)
                (Just a@(Left _), Just b) -> return $ TContext (Map.map (\tt -> if tt == a then b else tt) m, n)
                (Just a@(Right _), Just b@(Left _)) -> return $ TContext (Map.map (\tt -> if tt == b then a else tt) m, n)
                (Just (Right t1), Just (Right t2)) -> if t1 == t2 then return tc else throw (TypeUnificationException2 v1 t1 v2 t2)

toMap :: (Ord v) => TContext v t -> Map v (Maybe t)
toMap (TContext (m, _)) = Map.map eitherToMaybe m
        where
                eitherToMaybe (Left _) = Nothing
                eitherToMaybe (Right t) = Just t

firstFresh :: (Eq v, Ord v) => [v] -> TContext v t -> v
-- Returns the first element of the list that is fresh
firstFresh [] _ = error "firstFresh unable to find a fresh variable"
firstFresh (v:vs) tc@(TContext (m,_)) = if v `Map.member` m then firstFresh vs tc else v

difference :: (Eq v, Ord v) => TContext v t -> TContext v t -> TContext v t
difference (TContext (m1, i1)) (TContext (m2, _)) = TContext (Map.difference m1 m2, i1)
