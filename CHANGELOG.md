# 0.3.0.0
- Update to GHC 8.8.2 and singletons-2.6.

# 0.2.0.0

- Made NMap and NSum polymorphic over the kind of the key.  (Perhaps
  'Natural' keys would be useful as well.)  This is a breaking API
  change, because the qualifier for the kind of the key must go before
  the qualifier for the typelevel lists, potentially breaking
  TypeApplication uses.
- Add Eq and Ord instances for NMap and NSum
- Add a testsuite

# 0.1.0.1

Quickfix for an oversight in the `uninsertSum` function that broke
`splitSum`.

# 0.1.0.0

Initial release.  Expect the public-facing API to change as the
library is reworked.
