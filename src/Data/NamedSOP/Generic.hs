{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE AllowAmbiguousTypes            #-}
{-# LANGUAGE ScopedTypeVariables            #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.NamedSOP.Generic
  ( GenProduct(GProduct)
  -- , specProduct
  -- , genProduct
  ) where

import           Data.Kind
import           Data.Singletons.Prelude.Monoid
import           Data.Singletons.Prelude.Num
import           Data.Singletons.Prelude.Show
import           Data.Singletons.TypeLits
import Data.Singletons
import           GHC.Generics

import           Data.NamedSOP.Map

data TA = -- CA { fa :: Int } |
  CB Bool String
  deriving (Eq, Ord, Show, Generic)

data TB = CC { fd :: Int }
  deriving (Eq, Ord, Show, Generic)

class GenProduct (f :: * -> *) where
  type GProduct f :: [Mapping Symbol Type]
  genProduct' :: f a -> NMap (GProduct f)
  specProduct' :: NMap (GProduct f) -> f a

instance GenProduct f => GenProduct (D1 _a f) where
  type GProduct (D1 _a f) = GProduct f
  genProduct'  = genProduct' . unM1
  specProduct' = M1 . specProduct'

instance GenProduct f => GenProduct (C1 ('MetaCons _a _b 'True) f) where
  type GProduct (C1 ( 'MetaCons _a _b 'True) f) = GProduct f
  genProduct'  = genProduct' . unM1
  specProduct' = M1 . specProduct'

instance GenProduct (S1 ('MetaSel ('Just n) _a _b _c) (Rec0 t)) where
  type GProduct (S1 ( 'MetaSel ( 'Just n) _a _b _c) (Rec0 t)) = '[n ':-> t]
  genProduct' (M1 (K1 c)) = NMapExt c NMapEmpty
  specProduct' (NMapExt c NMapEmpty) = M1 (K1 c)

instance (SingI (GProduct f), SingI (GProduct g),
          GenProduct f, GenProduct g) => GenProduct (f :*: g) where
  type GProduct (f :*: g) = Union (GProduct f) (GProduct g)
  genProduct' (x :*: y) = unionMap (genProduct' x, genProduct' y)
  specProduct' m =
    let (m1, m2) = ununionMap m in specProduct' m1 :*: specProduct' m2

instance GenProductN f => GenProduct (C1 ('MetaCons _a _b 'False) f) where
  type GProduct (C1 ( 'MetaCons _a _b 'False) f) = GProductN 1 f
  genProduct' (M1 x) = genProductN' (SNat @1) x

class GenProductN (f :: * -> *) where
  type GProductN (n :: Nat) f :: [Mapping Symbol Type]
  type GProductS f :: Nat
  sGProductS :: SNat (GProductS f)
  sGProductN :: Sing n -> Sing (GProductN n f)
  genProductN' :: Sing n -> f a -> NMap (GProductN n f)
  -- specProductN' :: NMap (GProductN n f) -> f a

instance GenProductN (S1 ('MetaSel 'Nothing _a _b _c) (Rec0 t)) where
  type GProductN n (S1 ( 'MetaSel 'Nothing _a _b _c) (Rec0 t)) = '[Mappend "_" (Show_ n) ':-> t]
  type GProductS (S1 ( 'MetaSel 'Nothing _a _b _c) (Rec0 t)) = 1
  sGProductS = SNat
  sGProductN sn = SCons (SMapping (sMappend (SSym @"_") (sShow_ sn))) SNil
  genProductN' _ (M1 (K1 c)) = NMapExt c NMapEmpty
  -- specProductN' (NMapExt c NMapEmpty) = M1 (K1 c)

instance (GenProductN f, GenProductN g) => GenProductN (f :*: g) where
  type GProductN n (f :*: g)
    = Union (GProductN n f) (GProductN (n + GProductS f) g)
  type GProductS (f :*: g) = GProductS f + GProductS g
  sGProductS = (sGProductS @f) %+ (sGProductS @g)
  sGProductN sn = sUnion (sGProductN @f sn) (sGProductN @g (sn %+ sGProductS @f))
  genProductN' sn (x :*: y) =
    let (m1, m2) = (genProductN' sn x, genProductN' (sn %+ sGProductS @f) y)
        (sm1, sm2) = (sGProductN @f sn, sGProductN @g (sn %+ sGProductS @f))
    in withSingI sm1 $ withSingI sm2 $ unionMap (m1, m2)

-- genProduct :: (Generic a, GenProduct (Rep a)) => a -> NMap (GProduct (Rep a))
-- genProduct = genProduct' . from

-- specProduct :: (Generic a, GenProduct (Rep a)) => NMap (GProduct (Rep a)) -> a
-- specProduct = to . specProduct'

-- class GenSum (f :: * -> *) where
--   type GSum f

-- instance GeneralizeSum f => GeneralizeSum (D1 m f) where

-- instance GeneralizeSum (C1 ('MetaSel ('Just n) _a _b _c) f) where
