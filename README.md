# symbol-sets

`symbol-sets` provides type-level sets of `Symbols` using
[`GHC.TypeLits`](http://hackage.haskell.org/package/base-4.11.1.0/docs/GHC-TypeLits.html#Symbol):

## Type safety

`Set` is a type-level set that is correct by construction:

```haskell
λ> set :: Set '["x", "y", "z"]
Set ["x","y","z"]

λ> set :: Set '["x", "z", "y"]
<interactive>:142:1: error:
    • Couldn't match type ‘'GT’ with ‘'LT’ arising from a use of ‘set’
    • In the expression: set :: Set '["x", "z", "y"]
      In an equation for ‘it’: it = set :: Set '["x", "z", "y"]
```

## Set operations

Currently supported operations include:
- `head`
- `tail`
- `uncons`
- `union`
- `elem`
- `insert`

Currently supported instances include:
- `Eq`
- `Ord`
- `Show`
- `Read`
- `IsList`
