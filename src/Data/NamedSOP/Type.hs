{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE QuasiQuotes          #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-|
module      : Data.NamedSOP.Type
description : Symbol-type mappings, convenience re-exports

End users should not have to manually import this module, since it is
re-exported by "Data.NamedSOP.Map" and "Data.NamedSOP.Sum".

In addition to 'Mapping' and its related singletons, various type
families related to lists are redefined here, since the ones in
"Data.Singletons.Prelude.List" use local definitions.  [As of
2019-07](https://github.com/goldfirere/singletons/issues/339), it is
not possible to prove around local definitions that are promoted with
'singletons', so we are stuck redefining them.
-}
module Data.NamedSOP.Type
  ( -- * Symbol-value mappings
    Mapping(..)
  , SMapping(..)
    -- * List operation singletons
    -- | Unlike the usual definition, this 'union' does /not/ remove
    -- duplicates, since that would make it impossible to define a
    -- union operation for sums.
  , Union
  , sUnion
  , union
  , type (++)
  , (%++)
  , Insert
  , sInsert
  , insert
  , Sort
  , sSort
  , sort
    -- * Convenience re-exports
  , SingI
  , Sing
  , SList(..)
  ) where

import           Data.Singletons.Prelude.List (SList (..))
import           Data.Singletons.TH

singletons [d|
   (++) :: [a] -> [a] -> [a]
   [] ++ ys = ys
   (x:xs) ++ ys = x : (xs ++ ys)

   insert :: Ord a => a -> [a] -> [a]
   insert x [] = [x]
   insert x (y:ys) = case compare x y of
     LT -> x : y : ys
     EQ -> x : y : ys
     GT -> y : insert x ys

   sort :: Ord a => [a] -> [a]
   sort []     = []
   sort (x:xs) = insert x (sort xs)

   union :: Ord a => [a] -> [a] -> [a]
   union xs ys = sort (xs ++ ys)
 |]

-- | A type @v@ with an associated tag @k@.  Importantly, its
-- singleton data instance only takes a singleton for the tag @k@ as
-- its argmuent, and not one for the value @v@.
infixr 4 :->

data Mapping k v =
  k :-> v
  deriving (Show)

instance Eq a => Eq (Mapping a b) where
  (x :-> _) == (y :-> _) = x == y

instance Ord a => Ord (Mapping a b) where
  compare (x :-> _) (y :-> _) = compare x y

data SMapping (a :: Mapping k v) where
  SMapping :: Sing k -> SMapping (k ':-> v)

type instance Sing = SMapping

instance SingI k => SingI (k ':-> v) where
  sing = SMapping sing

-- | Equality and ordering on mappings uses only the key.
instance PEq (Mapping k v) where
  type (k1 ':-> _) == (k2 ':-> _) = k1 == k2

instance SEq k => SEq (Mapping k v) where
  (SMapping k1) %== (SMapping k2) = k1 %== k2

instance POrd k => POrd (Mapping k v) where
  type Compare (k1 ':-> _) (k2 ':-> _) = Compare k1 k2

instance SOrd k => SOrd (Mapping k v) where
  sCompare (SMapping k1) (SMapping k2) = sCompare k1 k2
