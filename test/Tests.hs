{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TypeApplications         #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE PolyKinds         #-}

import           Control.Monad
import           GHC.Generics
import           Test.Tasty
import           Test.Tasty.HUnit

import           Data.NamedSOP.Generic
import           Data.NamedSOP.Map
import           Data.NamedSOP.Sum

main :: IO ()
main = defaultMain tests

testGenSpecProd :: ( Generic a
                   , GenProduct (Rep a)
                   , Eq a
                   , Eq (NMap (GProduct (Rep a)))
                   , Show a
                   , Show (NMap (GProduct (Rep a)))) =>
  [Char] -> a -> NMap (GProduct (Rep a)) -> [TestTree]
testGenSpecProd s a b =
  [ testCase ("Generalize " ++ s) $
    genProduct a @?= b
  , testCase ("Specialize " ++ s) $
    specProduct b @?= a
  ]


testGenSpecSum :: ( Generic a
                   , GenSum (Rep a)
                   , Eq a
                   , Eq (NSum (GSum (Rep a)))
                   , Show a
                   , Show (NSum (GSum (Rep a)))) =>
  [Char] -> a -> NSum (GSum (Rep a)) -> [TestTree]
testGenSpecSum s a b =
  [ testCase ("Generalize " ++ s) $
    genSum a @?= b
  , testCase ("Specialize " ++ s) $
    specSum b @?= a
  ]

tests :: TestTree
tests = testGroup "Unit tests" [isoTests, unionTests]

data EmptyP = EmptyP
  deriving (Eq, Ord, Show, Generic)

data UnaryP a = UnaryP a
  deriving (Eq, Ord, Show, Generic)

data Size2P a b = Size2P a b
  deriving (Eq, Ord, Show, Generic)

data RecordP = RecordP { recordPA :: Int, recordPB :: String }
  deriving (Eq, Ord, Show, Generic)

data EmptyS
  deriving (Eq, Ord, Show, Generic)

data UnaryS a = UnaryS a
  deriving (Eq, Ord, Show, Generic)

data Size2S a b = Size2SA a
                | Size2SB b
  deriving (Eq, Ord, Show, Generic)

data RecordS = RecordSA { recordSAA :: Int }
             | RecordSB { recordSBA :: Bool, recordSBB :: String }
  deriving (Eq, Ord, Show, Generic)

isoTests :: TestTree
isoTests = testGroup "Generic isomorphisms" $ join $
  [ testGenSpecProd "empty product"
    EmptyP
    NMapEmpty
  , testGenSpecProd "unary product"
    (UnaryP True)
    (NMapExt @"_1" True NMapEmpty)
  , testGenSpecProd "size-2 product"
    (Size2P True "hello")
    (NMapExt @"_1" True (NMapExt @"_2" "hello" NMapEmpty))
  , testGenSpecProd "record product"
    (RecordP { recordPA = 1, recordPB = "hello" })
    (NMapExt @"recordPA" 1 (NMapExt @"recordPB" "hello" NMapEmpty))
  , testGenSpecSum "empty sum"
    (undefined :: EmptyS)
    (undefined :: NSum '[])
  , testGenSpecSum "unary sum"
    (UnaryS True)
    (NSumThis @"_UnaryS" (NMapExt @"_1" True NMapEmpty))
  , testGenSpecSum "size-2 sum, 1st branch"
    (Size2SA True :: Size2S Bool String)
    (NSumThis @"_Size2SA" (NMapExt @"_1" True NMapEmpty))
  , testGenSpecSum "size-2 sum, 2nd branch"
    (Size2SB "hello" :: Size2S Bool String)
    (NSumThat (NSumThis @"_Size2SB" (NMapExt @"_1" "hello" NMapEmpty)))
  , testGenSpecSum "sum of records, 1st branch"
    (RecordSA { recordSAA = 1 })
    (NSumThis @"_RecordSA" (NMapExt @"recordSAA" 1 NMapEmpty))
  , testGenSpecSum "sum of records, 2nd branch"
    (RecordSB { recordSBA = True, recordSBB = "hello" })
    (NSumThat (NSumThis @"_RecordSB"
               (NMapExt @"recordSBA" True
                (NMapExt @"recordSBB" "hello" NMapEmpty))))
  ]

unionTests :: TestTree
unionTests = testGroup "Union/ununion operations"
  [ testCase "Union of products" $
    unionMap
    ((NMapExt @"c" True (NMapExt @"a" "hello" NMapEmpty)),
     (NMapExt @"b" "world" (NMapExt @"d" False NMapEmpty)))
    @?=
    (NMapExt @"a" "hello"
     (NMapExt @"b" "world"
      (NMapExt @"c" True
       (NMapExt @"d" False NMapEmpty))))
  , testCase "Product ununion . union == id" $
    ununionMap
    (unionMap
     ((NMapExt @"c" True (NMapExt @"a" "hello" NMapEmpty)),
      (NMapExt @"b" "world" (NMapExt @"d" False NMapEmpty))))
    @?=
    ((NMapExt @"c" True (NMapExt @"a" "hello" NMapEmpty)),
     (NMapExt @"b" "world" (NMapExt @"d" False NMapEmpty)))
  , testCase "Union of sums, 1st branch" $
    unionSum @_ @'["b" ':-> Bool] @'["a" ':-> Int]
    (Left (NSumThis @"b" True))
    @?=
    (NSumThat (NSumThis @"b" True))
  , testCase "Union of sums, 2nd branch" $
    unionSum @_ @'["b" ':-> Bool] @'["a" ':-> Int]
    (Right (NSumThis @"a" 1))
    @?=
    (NSumThis @"a" 1)
  , testCase "Sum ununion . union == id" $
    ununionSum @_ @'["b" ':-> Bool] @'["a" ':-> Int]
    (unionSum @_ @'["b" ':-> Bool] @'["a" ':-> Int]
     (Left (NSumThis @"b" True)))
    @?=
    (Left (NSumThis @"b" True))
  ]
