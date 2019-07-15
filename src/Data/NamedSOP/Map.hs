{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

{-|
module      : Data.NamedSOP.Map
description : Dependently-typed products/maps
-}
module Data.NamedSOP.Map
  ( NMap(..)
  , unionMap
  , ununionMap
  , module Data.NamedSOP.Type
  ) where

import           GHC.TypeLits

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude.Ord

import           Data.NamedSOP.Type

-- | A depedently-typed product, or map.  The following are roughly
-- equivalent:
--
-- > type A = NMap '[ "a" ':-> Int, "b" ':-> Bool ]
-- > data A = A { a :: Int, b :: Bool }
data NMap :: [Mapping s Type] -> Type where
  NMapEmpty :: NMap '[]
  NMapExt :: forall k v xs. v -> NMap xs -> NMap ((k ':-> v) : xs)

-- Helper typeclasses for showing a map

class ShowMap xs where
  showMap :: NMap xs -> String

instance ShowMap '[ ] where
  showMap NMapEmpty = ""

instance {-# OVERLAPPABLE #-} (KnownSymbol k, Show v) =>
  ShowMap '[ k ':-> v ] where
  showMap (NMapExt v NMapEmpty) =
    symbolVal (Proxy :: Proxy k) ++ " :-> " ++ show v

instance {-# OVERLAPS #-} (KnownSymbol k, Show v, ShowMap xs) =>
  ShowMap ((k ':-> v) ': xs) where
  showMap (NMapExt v xs) =
    symbolVal (Proxy :: Proxy k) ++ " :-> " ++ show v ++ ", " ++ showMap xs

instance ShowMap xs => Show (NMap xs) where
  show xs = "{ " ++ showMap xs ++ " }"

appendMap :: NMap xs -> NMap ys -> NMap (xs ++ ys)
appendMap NMapEmpty ys      = ys
appendMap (NMapExt x xs) ys = NMapExt x (appendMap xs ys)

insertMap :: forall s k v (xs :: [Mapping s *]). SOrd s
  => Sing (k ':-> v) -> Sing xs -> v -> NMap xs -> NMap (Insert (k ':-> v) xs)
insertMap _ _ x NMapEmpty = NMapExt x NMapEmpty
insertMap sxk (SCons syk sys) x ys@(NMapExt y ys') =
  case sCompare sxk syk of
    SLT -> NMapExt x ys
    SEQ -> NMapExt x ys
    SGT -> NMapExt y (insertMap sxk sys x ys')

sortMap :: forall s (xs :: [Mapping s *]). SOrd s
  => Sing xs -> NMap xs -> NMap (Sort xs)
sortMap _ NMapEmpty = NMapEmpty
sortMap (SCons sx sxs) (NMapExt x xs) =
  insertMap sx (sSort sxs) x (sortMap sxs xs)

-- | Combine two 'NMap's in a way such that the original ordering of
-- their fields doesn't matter; no matter how you combine smaller maps
-- to create a large one, you are guaranteed to have a sorted 'NMap'
-- when you finish.
--
-- 'NMap's form a commutative monoid under 'unionMap', with
-- 'NMapEmpty' as the identity.
--
-- This function takes a tuple as an argument so that it is symmetric
-- with `ununionMap`.
unionMap ::
     forall s (xs :: [Mapping s *]) (ys :: [Mapping s *]). (SingI xs, SingI ys, SOrd s)
  => (NMap xs, NMap ys)
  -> NMap (Union xs ys)
unionMap (xs, ys) = sortMap (sing @xs %++ sing @ys) (appendMap xs ys)

splitMap :: forall xs ys. Sing xs -> Sing ys -> NMap (xs ++ ys) -> (NMap xs, NMap ys)
splitMap SNil SNil NMapEmpty = (NMapEmpty, NMapEmpty)
splitMap SNil _ x = (NMapEmpty, x)
splitMap (SCons _ sxs) sys (NMapExt x xs) =
  let (a, b) = splitMap sxs sys xs
  in (NMapExt x a, b)

uninsertMap :: forall s k v (xs :: [Mapping s *]). SOrd s
  => Sing (k ':-> v) -> Sing xs -> NMap (Insert (k ':-> v) xs) -> (v, NMap xs)
uninsertMap _ SNil (NMapExt v NMapEmpty) = (v, NMapEmpty)
uninsertMap sx@(SMapping sk) (SCons (SMapping sk') sxs) (NMapExt v vs) = case sCompare sk sk' of
  SLT -> (v, vs)
  SEQ -> (v, vs)
  SGT -> let (v', vs') = uninsertMap sx sxs vs
        in (v', NMapExt v vs')
uninsertMap _ (SCons _ _) NMapEmpty = error "unreachable"

unsortMap :: forall s (xs :: [Mapping s *]). SOrd s
  => Sing xs -> NMap (Sort xs) -> NMap xs
unsortMap SNil NMapEmpty = NMapEmpty
unsortMap (SCons sx@(SMapping _) sxs) vs =
  let (v', vs') = uninsertMap sx (sSort sxs) vs
  in NMapExt v' (unsortMap sxs vs')

-- | Split a sorted 'NMap' into two arbitrary (and potentially
-- unsorted) submaps.  Conveniently select the submaps to split into
-- using @-XTypeApplications@.  (Note the empty type argument for the
-- key kind).
--
-- >>> m :: NMap '[ "a" ':-> Int, "b" ':-> Bool, "c" ':-> String ]
-- >>> m = NMapExt 1 (NMapExt True (NMapExt "hello" NMapEmpty))
-- >>> ununionMap @_ @'[ "b" ':-> Bool, "a" ':-> Int ] @'[ "c" ':-> String ] m
-- ({ b :-> True, a :-> 1 },{ c :-> "hello" })
ununionMap :: forall s (xs :: [Mapping s *]) (ys :: [Mapping s *]). (SingI xs, SingI ys, SOrd s)
  => NMap (Union xs ys) -> (NMap xs, NMap ys)
ununionMap vs = splitMap sxs sys (unsortMap (sxs %++ sys) vs)
  where
    sxs = sing @xs
    sys = sing @ys
