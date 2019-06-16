# generics-gadt

## What is this?

Have you ever wondered if [GHC.Generics](http://hackage.haskell.org/package/base-4.12.0.0/docs/GHC-Generics.html)
could be extended to cover existential types and GADTs? Not really? Never mind, in any case, this is an attempt
to answer that question in the affirmative.

## Does it work?

It is still work in progress, but you can already check the [examples](examples) to see it in action. Here's
a snippet from the [Vector example](examples/src/Vector.hs): 

```haskell
data Peano
  = Z
  | Succ Peano

data Vector (n :: Peano) (a :: Type) where
    VecZ :: Vector 'Z a
    VecS :: a -> Vector n a -> Vector ('Succ n) a
    
# manual definition for now
instance Generic (Vector n a) where  ...

instance GShow a => GShow (Vector n a)
instance GEq a => GEq (Vector n a)
instance GSemigroup (Vector 'Z a)
instance (GSemigroup a, GSemigroup (Vector n a)) => GSemigroup (Vector ('Succ n) a)
instance GMonoid (Vector 'Z a)
instance (GMonoid a, GMonoid (Vector n a)) => GMonoid (Vector ('Succ n) a)
```

Here, `GShow`, `GEq`, `GSemigroup` and `GMonoid` come from the
[generic-deriving](https://hackage.haskell.org/package/generic-deriving), augmented
with additional instances (see [generic-deriving-exts](generic-deriving-exts)) for
the types defined in this package.

Particularly interesting are the `GSemigroup` and `GMonoid` instances, since
the generic representation of `Vector n a` involves a sum `:*:`, which the generic
definitions of `GSemigrouop` and `GMonoid` of course can't handle! The trick
here is that `Vector 'Z a` and `Vector ('S n) a` can both be treated as if they
had no sums in their representation...

## How does it work?

We use a GADT to represent existential formulas in prenex normal-form with free-variables.
The free variables within the type, in combination with the `QuantifiedConstraints` extension
let us eliminate existentially quantified variables in instance declarations. Moreover, this
type includes two existential constructors: one for GADT-style existentials, where the
quantified type appears in the type of the GADT (like `n` in the `VecS` constructor above)
and one for non-GADT existential-quantification. This allow us, e.g., to get an instance
`GEq (Vector n a)`: otherwise, after peeling the existential quantifier for `n` the compiler
wouldn't be able to prove that `n` must be the same both on the left and right hand of the
`geq` function being defined.

## Known limitations

We use a type-family to implement substitutions of (type-level representation of) "variables" by
types, but this cannot observe occurrences of "variables" under type-families (since they are
non-matchable). Because of this, we currently cannot provide a generic instance for this
variation of `Vector` above:

```haskell
data Vector (n :: Nat) (a :: Type) where
    VecZ :: Vector 0 a
    VecS :: a -> Vector n a -> Vector (n + 1) a
```

We could eventually leverage on [UnsaturatedTypeFamilies](https://github.com/ghc-proposals/ghc-proposals/pull/242)
to lift this restriction.

## Roadmap

  - Define TH code to derive `Generic` instances for GADTs and existential types, since at
    the moment is quite a bit of work to experiment with new cases.
  - Clean-up the API, try to make writing of instances for generic functions clearer.
  - Documentation.
