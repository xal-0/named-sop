{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Data.NamedSOP.Map
  ( NMap(..)
  , unionMap
  , splitMap
  , module Data.NamedSOP.Type
  ) where

import           GHC.TypeLits

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude.List hiding (Union)
import           Data.Singletons.Prelude.Ord

import           Data.NamedSOP.Type

import           Unsafe.Coerce

data NMap :: [Mapping Symbol Type] -> Type where
  NMapEmpty :: NMap '[]
  NMapExt :: forall k v xs. v -> NMap xs -> NMap ((k ':-> v) : xs)

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

insertMap ::
     Sing (k ':-> v) -> Sing xs -> v -> NMap xs -> NMap (Insert (k ':-> v) xs)
insertMap _ _ x NMapEmpty = NMapExt x NMapEmpty
insertMap sxk (SCons syk sys) x ys@(NMapExt y ys') =
  case sCompare sxk syk of
    SLT -> NMapExt x ys
    SEQ -> NMapExt x ys
    SGT -> NMapExt y (insertMap sxk sys x ys')

sortMap :: Sing xs -> NMap xs -> NMap (Sort xs)
sortMap _ NMapEmpty = NMapEmpty
sortMap (SCons sx sxs) (NMapExt x xs) =
  unsafeCoerce $ insertMap sx (sSort sxs) x (sortMap sxs xs)
  -- Necessary because of https://github.com/goldfirere/singletons/issues/339

unionMap ::
     forall xs ys. (SingI xs, SingI ys)
  => NMap xs
  -> NMap ys
  -> NMap (Union xs ys)
unionMap xs ys = sortMap (sing @xs %++ sing @ys) (appendMap xs ys)

splitMap' :: forall xs ys. Sing xs -> Sing ys -> NMap (xs ++ ys) -> (NMap xs, NMap ys)
splitMap' SNil SNil NMapEmpty = (NMapEmpty, NMapEmpty)
splitMap' SNil _ x = (NMapEmpty, x)
splitMap' (SCons _ sxs) sys (NMapExt x xs) =
  let (a, b) = splitMap' sxs sys xs
  in (NMapExt x a, b)

splitMap :: forall xs ys. (SingI xs, SingI ys) => NMap (xs ++ ys) -> (NMap xs, NMap ys)
splitMap = splitMap' sing sing
