# named-sop: Dependently-typed sums and products, tagged by field name

[![Hackage](https://img.shields.io/hackage/v/named-sop.svg)](https://hackage.haskell.org/package/named-sop)
[![Build Status](https://secure.travis-ci.org/sjsch/named-sop.svg)](http://travis-ci.org/sjsch/named-sop)

Sums and Maps (products) indexed by a typelevel map of their field
(or constructor) names and types.  They can be combined and split
again; their typelevel map is sorted to ensure that the end result
is independent of the order you combine it in.

"Data.NamedSOP.Generic" contains functions for automatically
converting between types with a Generic instance and named sums of
products:

```haskell
>>> data A = C { a :: Int, b :: Bool } 
>>>          | D Int Bool deriving (Generic)
>>> :t genSum (C 3 True)
NSum
 '[ "_C" ':-> NMap '[ "a" ':-> Int, "b" ':-> Bool],
    "_D" ':-> NMap '[ "_1" ':-> Int, "_2" ':-> Bool]]
```
