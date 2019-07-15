{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-|
module      : Data.NamedSOP.Generic
description : Convert to/from Generic instances and named sums of products
-}
module Data.NamedSOP.Generic
  ( genProduct
  , specProduct
  , genSum
  , specSum
  , GenProduct(GProduct)
  , GenSum(GSum)
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude.Monoid
import           Data.Singletons.Prelude.Num
import           Data.Singletons.Prelude.Show
import           Data.Singletons.TypeLits
import           GHC.Generics

import           Data.NamedSOP.Map
import           Data.NamedSOP.Sum

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

instance GenProduct U1 where
  type GProduct U1 = '[]
  genProduct' U1 = NMapEmpty
  specProduct' NMapEmpty = U1

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
  specProduct' x = M1 (specProductN' (SNat @1) x)

class GenProductN (f :: * -> *) where
  type GProductN (n :: Nat) f :: [Mapping Symbol Type]
  type GProductS f :: Nat
  sGProductS :: SNat (GProductS f)
  sGProductN :: Sing n -> Sing (GProductN n f)
  genProductN' :: Sing n -> f a -> NMap (GProductN n f)
  specProductN' :: Sing n -> NMap (GProductN n f) -> f a

instance GenProductN U1 where
  type GProductN n U1 = '[]
  type GProductS U1 = 0
  sGProductS = SNat
  sGProductN _ = SNil
  genProductN' _ U1 = NMapEmpty
  specProductN' _ NMapEmpty = U1

instance GenProductN (S1 ('MetaSel 'Nothing _a _b _c) (Rec0 t)) where
  type GProductN n (S1 ( 'MetaSel 'Nothing _a _b _c) (Rec0 t)) = '[Mappend "_" (Show_ n) ':-> t]
  type GProductS (S1 ( 'MetaSel 'Nothing _a _b _c) (Rec0 t)) = 1
  sGProductS = SNat
  sGProductN sn = SCons (SMapping (sMappend (SSym @"_") (sShow_ sn))) SNil
  genProductN' _ (M1 (K1 c)) = NMapExt c NMapEmpty
  specProductN' _ (NMapExt c NMapEmpty) = M1 (K1 c)

instance (GenProductN f, GenProductN g) => GenProductN (f :*: g) where
  type GProductN n (f :*: g)
    = Union (GProductN n f) (GProductN (n + GProductS f) g)
  type GProductS (f :*: g) = GProductS f + GProductS g
  sGProductS = sGProductS @f %+ sGProductS @g
  sGProductN sn =
    sUnion (sGProductN @f sn) (sGProductN @g (sn %+ sGProductS @f))
  genProductN' sn (x :*: y) =
    let (m1 , m2 ) = (genProductN' sn x, genProductN' (sn %+ sGProductS @f) y)
        (sm1, sm2) = (sGProductN @f sn, sGProductN @g (sn %+ sGProductS @f))
    in  withSingI sm1 $ withSingI sm2 $ unionMap (m1, m2)
  specProductN' (sn :: Sing n) m =
    let (sm1, sm2) = (sGProductN @f sn, sGProductN @g (sn %+ sGProductS @f))
        (x, y) =
            withSingI sm1
              $ withSingI sm2
              $ ununionMap @(GProductN n f) @(GProductN (n + GProductS f) g) m
    in  specProductN' sn x :*: specProductN' (sn %+ sGProductS @f) y

class GenSum (f :: * -> *) where
  type GSum f :: [Mapping Symbol Type]
  genSum' :: f a -> NSum (GSum f)
  specSum' :: NSum (GSum f) -> f a

instance GenSum f => GenSum (D1 _a f) where
  type GSum (D1 _a f) = GSum f
  genSum'  = genSum' . unM1
  specSum' = M1 . specSum'

instance GenSum V1 where
  type GSum V1 = '[]
  genSum' _ = error "unreachable"
  specSum' _ = error "unreachable"

instance GenProduct f => GenSum (C1 ('MetaCons n _a 'True) f) where
  type GSum (C1 ( 'MetaCons n _a 'True) f) = '[Mappend "_" n ':-> NMap (GProduct f)]
  genSum' (M1 x) = NSumThis (genProduct' x)
  specSum' (NSumThis x) = M1 (specProduct' x)
  specSum' (NSumThat _) = error "unreachable"

instance GenProductN f => GenSum (C1 ('MetaCons n _a 'False) f) where
  type GSum (C1 ( 'MetaCons n _a 'False) f) = '[Mappend "_" n ':-> NMap (GProductN 1 f)]
  genSum' (M1 x) = NSumThis (genProductN' (SNat @1) x)
  specSum' (NSumThis x) = M1 (specProductN' (SNat @1) x)
  specSum' (NSumThat _) = error "unreachable"

instance ( SingI (GSum f), SingI (GSum g)
         , GenSum f, GenSum g) => GenSum (f :+: g) where
  type GSum (f :+: g) = Union (GSum f) (GSum g)
  genSum' (L1 x) = unionSum @(GSum f) @(GSum g) (Left (genSum' x))
  genSum' (R1 x) = unionSum @(GSum f) @(GSum g) (Right (genSum' x))
  specSum' m = case ununionSum @(GSum f) @(GSum g) m of
    Left  x -> L1 (specSum' x)
    Right y -> R1 (specSum' y)

-- | Convert a single-constructor type with a 'Generic' instance into
-- a sorted 'NMap'.  Constructors with record selectors will use their
-- names, and constructors without will use numbers, prefixed with @_@
-- for better compatibility with @-XOverloadedLabels@.
--
-- >>> data A = C { a :: Int, b :: Bool } deriving (Generic)
-- >>> genProduct (C { a = 1, b = True })
-- { a :-> 1, b :-> True }
--
-- >>> data B = D Int Bool deriving (Generic)
-- >>> genProduct (D 1 True)
-- { _1 :-> 1, _2 :-> True }
genProduct :: (Generic a, GenProduct (Rep a)) => a -> NMap (GProduct (Rep a))
genProduct = genProduct' . from

-- | Reverse the operation performed by 'genProduct'.
specProduct :: (Generic a, GenProduct (Rep a)) => NMap (GProduct (Rep a)) -> a
specProduct = to . specProduct'

-- | Convert a type with a generic instance with any number of
-- constructors into an 'NSum' of 'NMap's.  All constructor names will
-- be prefixed with @_@ to allow for the use of @-XOverloadedLabels@.
--
-- >>> data A = C { a :: Int, b :: Bool } | D Int Bool deriving (Generic)
-- >>> :t genSum (C 3 True)
-- NSum
--  '[ "_C" ':-> NMap '[ "a" ':-> Int, "b" ':-> Bool],
--     "_D" ':-> NMap '[ "_1" ':-> Int, "_2" ':-> Bool]]
genSum :: (Generic a, GenSum (Rep a)) => a -> NSum (GSum (Rep a))
genSum = genSum' . from

-- | Reverse the operation performed by 'genSum'.
specSum :: (Generic a, GenSum (Rep a)) => NSum (GSum (Rep a)) -> a
specSum = to . specSum'
