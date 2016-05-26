{-# LANGUAGE DeriveFunctor, TypeFamilies, FlexibleInstances, MultiParamTypeClasses #-}
{- Provide maps with aliasing.
 - The purpose is to support handling of shared regions.
 - Some region variables may be aliases for each other.
 - Some may be aliased, but we don't know it (and later
 - come to know it).
 - Some may definitely not be aliases.
 -}

module Caper.Utils.AliasingMap where
import Prelude hiding (foldr, lookup)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (intercalate)
import Data.Maybe
import Data.Foldable
import Data.Traversable
import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Maybe
import Control.Lens


{- AliasMap.
 - Invariant: a key either maps to a value, or to another
 -      key that maps to a value.
 - In particular, there will be no chains of aliasing, and
 - certainly no cycles.  Neither shall there be 'dangling'
 - aliases.
 -}
newtype AliasMap a b = AliasMap (Map a (Either a b)) deriving (Functor)

instance Foldable (AliasMap a) where
        foldr f x0 (AliasMap m) = foldr f' x0 m
                where
                        f' (Left _) x = x
                        f' (Right y) x = f y x

instance Traversable (AliasMap a) where
        sequenceA (AliasMap m) = pure AliasMap <*> sequenceA (fmap el m)
                where
                        el (Left x) = pure (Left x)
                        el (Right y) = pure Right <*> y

instance (Show a, Show b, Eq a) => Show (AliasMap a b) where
        show (AliasMap m) = intercalate "," $ Map.foldWithKey ofold [] m
                where
                        ofold _ (Left _) = id
                        ofold k (Right v) = (:) ("{" ++ show k ++ Map.foldWithKey (ifold k) "" m ++ "} => " ++ show v)
                        ifold a k (Left x) = if a == x then (("," ++ show k) ++) else id
                        ifold _ _ (Right _) = id

type instance Index (AliasMap a b) = a
type instance IxValue (AliasMap a b) = b
instance (Ord a) => Ixed (AliasMap a b) where
        ix k f m = case lookup k m of
                Just v -> f v <&> \v' -> overwrite k v' m
                Nothing -> pure m

instance (Ord a) => FunctorWithIndex a (AliasMap a)
instance (Ord a) => FoldableWithIndex a (AliasMap a)
instance (Ord a) => TraversableWithIndex a (AliasMap a) where
    itraverse f (AliasMap m) = fmap AliasMap (itraverse f' m)
        where
            f' i (Left v) = pure (Left v)
            f' i (Right x) = fmap Right (f i x)
empty :: AliasMap a b
empty = AliasMap Map.empty

-- |Add new entry in the map
-- Pre: key should not already be in the map
insert :: (Ord a) => a -> b -> AliasMap a b -> AliasMap a b
insert k v (AliasMap m) = AliasMap $ Map.insertWith' (error "AliasMap.insert: attempted to add an entry where one already exists.") k (Right v) m

-- |Add a new key as an alias for an existing key
-- Pre: the new key should not be in the map, but the old key should
addAlias :: (Ord a) => a -> a -> AliasMap a b -> AliasMap a b
addAlias newk oldk (AliasMap m) = case Map.lookup oldk m of
                        Just (Left alias) -> upd alias
                        Just (Right _) -> upd oldk
                        Nothing -> error "AliasMap.addAlias: attempted to add an alias to something that doesn't exist."
        where
                upd alias = AliasMap $ Map.insertWith' (error "AliasMap.addAlias: attempted to add an entry where one already exists.") newk (Left alias) m

root :: (Ord a) => a -> AliasMap a b -> Maybe a
root key (AliasMap m) = case Map.lookup key m of
                        Just (Left alias) -> Just alias
                        Just (Right _) -> Just key
                        Nothing -> Nothing

lookup :: (Ord a) => a -> AliasMap a b -> Maybe b
lookup key (AliasMap m) = do
                        x <- Map.lookup key m
                        case x of
                                Left alias -> 
                                        case Map.lookup alias m of
                                                Just (Right res) -> return res
                                                _ -> error "AliasingMap.lookup: ill-formed AliasMap."
                                Right res -> return res

resolve :: (Ord a) => a -> AliasMap a b -> Maybe (a, b)
resolve key (AliasMap m) = do
                        x <- Map.lookup key m
                        case x of
                                Left alias -> 
                                        case Map.lookup alias m of
                                                Just (Right res) -> return (alias, res)
                                                _ -> error "AliasingMap.resolve: ill-formed AliasMap."
                                Right res -> return (key, res)

rootDefault :: (Ord a) => a -> a -> AliasMap a b -> a
rootDefault def a = fromMaybe def . root a

overwrite :: (Ord a) => a -> b -> AliasMap a b -> AliasMap a b
overwrite key val am@(AliasMap m) =
        AliasMap $ Map.insert (rootDefault key key am) (Right val) m


-- Given two keys, renders them aliases.  If they are not already
-- aliases, then the values are merged with the given (monadic) operation.
-- Pre: the two keys must exist in the 
mergeAliases :: (MonadPlus m, Ord a) => (b -> b -> m b) -> a -> a -> AliasMap a b -> m (AliasMap a b)
mergeAliases mop k1 k2 am@(AliasMap m) = if k1' == k2' then return am else do
                        v <- mop v1 v2
                        return $ AliasMap $ Map.insert k2' (Left k1') $ Map.insert k1' (Right v) m
        where
                (k1', v1) = eresolve k1
                (k2', v2) = eresolve k2
                eresolve k = fromMaybe (error "mergeAliases: provided key does not exist") $ resolve k am

mergeAliasesM :: (Monad m, Ord a) => (b -> b -> m (Maybe b)) -> a -> a -> AliasMap a b -> m (Maybe (AliasMap a b))
mergeAliasesM mop k1 k2 am = runMaybeT $ mergeAliases (\x y -> MaybeT $ mop x y) k1 k2 am

-- |Returns a list of key-value pairs, where the key is a single
-- representative of each aliasing class
toRootList :: (Ord a) => AliasMap a b -> [(a,b)]
toRootList (AliasMap m) = Map.foldWithKey scq [] m
        where
                scq _ (Left _) = id
                scq k (Right v) = ((k, v) :)

-- |Returns a list of distinct keys. Any key in the map will be an alias
-- for one of them.
distinctKeys :: (Ord a) => AliasMap a b -> [a]
distinctKeys = map fst . toRootList

areAliases :: (Ord a) => a -> a -> AliasMap a b -> Bool
areAliases k1 k2 (AliasMap m) = k1 == k2 || case Map.lookup k1 m of
        Nothing -> False
        Just (Left k1') -> k1 == k2 || case Map.lookup k2 m of
                Just (Left k2') -> k1' == k2'
                _ -> False
        Just (Right _) -> case Map.lookup k2 m of
                Just (Left k2') -> k1 == k2'
                _ -> False
