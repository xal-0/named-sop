{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

{-|
module      : Data.NamedSOP.Sum
description : Dependently-typed sums
-}
module Data.NamedSOP.Sum
  ( NSum(..)
  , unionSum
  , ununionSum
  , module Data.NamedSOP.Type
  ) where

import           GHC.TypeLits

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude.Ord

import           Data.NamedSOP.Type

-- | A dependently-typed sum.  The following are roughly equilvalent:
--
-- > type A = NSum '[ "B" ':-> Int, "C" ':-> Bool ]
-- > data A = B Int | C Bool
data NSum :: [Mapping Symbol Type] -> Type where
  NSumThis :: v -> NSum ((k ':-> v) ': xs)
  NSumThat :: forall x xs. NSum xs -> NSum (x ': xs)

instance {-# OVERLAPPABLE #-} Show (NSum '[]) where
  show _ = error "unreachable"

instance {-# OVERLAPS #-} (KnownSymbol k, Show v, Show (NSum xs)) =>
  Show (NSum ((k ':-> v) ': xs)) where
  show (NSumThis v)  = symbolVal (Proxy :: Proxy k) ++ " :-> " ++ show v
  show (NSumThat vs) = show vs

appendSum :: Sing xs -> Sing ys -> Either (NSum xs) (NSum ys) -> NSum (xs ++ ys)
appendSum _ _ (Left (NSumThis x)) = NSumThis x
appendSum (SCons _ sxs) sys (Left (NSumThat xs)) = NSumThat (appendSum sxs sys (Left xs))
appendSum SNil _ (Right ys) = ys
appendSum (SCons (_ :: Sing x) sxs) sys (Right ys) = NSumThat @x (appendSum sxs sys (Right ys))

insertSum :: Sing (k ':-> v) -> Sing xs -> Either v (NSum xs) -> NSum (Insert (k ':-> v) xs)
insertSum _ SNil (Left v) = NSumThis v
insertSum sxk (SCons syk sys) (Left v) =
  case sCompare sxk syk of
    SLT -> NSumThis v
    SEQ -> NSumThis v
    SGT -> NSumThat (insertSum sxk sys (Left v))
insertSum sxk (SCons syk sys) (Right v) = case sCompare sxk syk of
  SLT -> NSumThat v
  SEQ -> NSumThat v
  SGT -> case v of
    NSumThis v' -> NSumThis v'
    NSumThat v' -> NSumThat (insertSum sxk sys (Right v'))
insertSum _ SNil (Right _) = error "unreachable"

sortSum :: Sing xs -> NSum xs -> NSum (Sort xs)
sortSum SNil _                      = error "unreachable"
sortSum (SCons sx sxs) (NSumThis v) = insertSum sx (sSort sxs) (Left v)
sortSum (SCons sx@(SMapping _) sxs) (NSumThat vs) =
  insertSum sx (sSort sxs) (Right (sortSum sxs vs))

-- | Combine two 'NSum's.  This is dual to
-- 'Data.NamedSOP.Map.unionMap', which accepts a product of products
-- and returns a product; 'unionSum' accepts a sum of sums and returns
-- a sum.  The order of fields does not matter, because they will be
-- sorted.
--
-- 'NSum's form a commutative monoid under 'unionSum', with @NSum '[]@
-- as the identity.
--
-- Together with 'Data.NamedSOP.Map.NMap',
-- 'Data.NamedSOP.Map.NMapEmpty', and 'Data.NamedSOP.Map.unionMap', it
-- is a semiring.
unionSum ::
     forall xs ys. (SingI xs, SingI ys)
  => Either (NSum xs) (NSum ys)
  -> NSum (Union xs ys)
unionSum xs = sortSum (sing @xs %++ sing @ys) (appendSum (sing @xs) (sing @ys) xs)

splitSum :: forall xs ys. Sing xs -> Sing ys
  -> NSum (xs ++ ys) -> Either (NSum xs) (NSum ys)
splitSum SNil SNil _ = error "unreachable"
splitSum SNil _ s = Right s
splitSum (SCons _ _) _ (NSumThis v) = Left (NSumThis v)
splitSum (SCons _ sxs) sys (NSumThat v) =
  case splitSum sxs sys v of
    Left x  -> Left (NSumThat x)
    Right x -> Right x

uninsertSum :: forall k v xs. Sing (k ':-> v) -> Sing xs
  -> NSum (Insert (k ':-> v) xs) -> Either v (NSum xs)
uninsertSum _ SNil (NSumThis v) = Left v
uninsertSum _ SNil (NSumThat v) = Right v
uninsertSum sxk (SCons syk _) (NSumThis v) = case sCompare sxk syk of
  SLT -> Left v
  SEQ -> Left v
  SGT -> error "unsorted list"
uninsertSum sxk (SCons syk sys) (NSumThat vs) = case sCompare sxk syk of
  SLT -> Right vs
  SEQ -> Right vs
  SGT -> case uninsertSum sxk sys vs of
          Left x  -> Left x
          Right x -> Right (NSumThat x)

unsortSum :: forall xs. Sing xs -> NSum (Sort xs) -> NSum xs
unsortSum SNil _ = error "unreachable"
unsortSum (SCons sx@(SMapping _) sxs) v =
  case uninsertSum sx (sSort sxs) v of
    Left x  -> NSumThis x
    Right x -> NSumThat (unsortSum sxs x)

-- | Split a sorted 'NSum' into either of two (potentially unsorted)
-- subsums.  Select the subsums with @-XTypeApplications@.
--
-- >>> s :: NSum '[ "A" ':-> Int, "B" ':-> Bool, "C" ':-> String ]
-- >>> s = NSumThat (NSumThis True) -- Select the "B" field.
-- >>> ununionSum @'[ "B" ':-> Bool, "A" ':-> Int ] @'[ "C" ':-> String ] s
-- Left (B :-> True)
ununionSum :: forall xs ys. (SingI xs, SingI ys) =>
  NSum (Union xs ys) -> Either (NSum xs) (NSum ys)
ununionSum vs = splitSum sxs sys (unsortSum (sxs %++ sys) vs)
  where
    sxs = sing @xs
    sys = sing @ys
