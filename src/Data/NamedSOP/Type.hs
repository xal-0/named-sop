{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeInType    #-}
{-# LANGUAGE TypeOperators #-}

module Data.NamedSOP.Type
  ( Mapping(..)
  , Union
  , SMapping
  , SingI
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude.Eq
import           Data.Singletons.Prelude.List hiding (Union)
import           Data.Singletons.Prelude.Ord

type Union xs ys = Sort (xs ++ ys)

infixr 4 :->

data Mapping k v =
  k :-> v
  deriving (Show)

instance Eq a => Eq (Mapping a b) where
  (x :-> _) == (y :-> _) = x == y

instance Ord a => Ord (Mapping a b) where
  compare (x :-> _) (y :-> _) = compare x y

type SMapping = (Sing :: Mapping k v -> Type)

data instance  Sing (a :: Mapping k v) where
        SMapping :: Sing k -> Sing (k ':-> v)

instance SingI k => SingI (k ':-> v) where
  sing = SMapping sing

instance PEq (Mapping k v) where
  type (k1 ':-> _) == (k2 ':-> _) = k1 == k2

instance SEq k => SEq (Mapping k v) where
  (SMapping k1) %== (SMapping k2) = k1 %== k2

instance POrd k => POrd (Mapping k v) where
  type Compare (k1 ':-> _) (k2 ':-> _) = Compare k1 k2

instance SOrd k => SOrd (Mapping k v) where
  sCompare (SMapping k1) (SMapping k2) = sCompare k1 k2
