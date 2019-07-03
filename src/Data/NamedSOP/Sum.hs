{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Data.NamedSOP.Sum
  ( unionSum
  , splitSum
  , module Data.NamedSOP.Type
  ) where

import           GHC.TypeLits

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude.List hiding (Union)
import           Data.Singletons.Prelude.Ord

import           Unsafe.Coerce

import           Data.NamedSOP.Type

data NSum :: [Mapping Symbol Type] -> Type where
  NSumThis :: v -> NSum ((k ':-> v) ': xs)
  NSumThat :: forall x xs. NSum xs -> NSum (x ': xs)

appendSum :: Sing xs -> Sing ys -> Either (NSum xs) (NSum ys) -> NSum (xs ++ ys)
appendSum _ _ (Left (NSumThis x)) = NSumThis x
appendSum (SCons _ sxs) sys (Left (NSumThat xs)) = NSumThat (appendSum sxs sys (Left xs))
appendSum SNil _ (Right ys) = ys
appendSum (SCons (_ :: Sing x) sxs) sys (Right ys) = NSumThat @x (appendSum sxs sys (Right ys))

insertSum :: Sing (k ':-> v) -> Sing xs -> v -> NSum (Insert (k ':-> v) xs)
insertSum _ SNil v = NSumThis v
insertSum sxk (SCons syk sys) v =
  case sCompare sxk syk of
    SLT -> NSumThis v
    SEQ -> NSumThis v
    SGT -> NSumThat (insertSum sxk sys v)

sortSum :: Sing xs -> NSum xs -> NSum (Sort xs)
sortSum SNil _                      = error "unreachable"
sortSum (SCons sx sxs) (NSumThis v) = unsafeCoerce $ insertSum sx sxs v
sortSum (SCons _ sxs) (NSumThat v)  = unsafeCoerce $ sortSum sxs v
  -- Necessary because of https://github.com/goldfirere/singletons/issues/339

unionSum ::
     forall xs ys. (SingI xs, SingI ys)
  => Either (NSum xs) (NSum ys)
  -> NSum (Union xs ys)
unionSum xs = sortSum (sing @xs %++ sing @ys) (appendSum (sing @xs) (sing @ys) xs)

splitSum' :: forall xs ys. Sing xs -> Sing ys -> NSum (xs ++ ys) -> Either (NSum xs) (NSum ys)
splitSum' SNil SNil _ = error "unreachable"
splitSum' SNil _ s = Right s
splitSum' (SCons _ _) _ (NSumThis v) = Left (NSumThis v)
splitSum' (SCons _ sxs) sys (NSumThat v) =
  case splitSum' sxs sys v of
    Left x  -> Left (NSumThat x)
    Right x -> Right x

splitSum :: forall xs ys. (SingI xs, SingI ys) => NSum (xs ++ ys) -> Either (NSum xs) (NSum ys)
splitSum = splitSum' sing sing
