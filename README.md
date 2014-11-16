`monad-levels`
==============

Why not mtl?
------------

The oft-spouted problem with the standard monad transformer library
[mtl] and similar libraries is that instances are quadratic: you need
a separate instance for each valid combination of transformer +
typeclass.

mtl: http://hackage.haskell.org/package/mtl

For end users, this isn't really a problem: after all, all the
required instances have already been written for you!

But what happens if you have a custom transformer, or a custom
typeclass?

What about if you want to have something like `MonadIO` but for a
different base monad?

Then you need to write all those extra instances.

What makes it more frustrating is that many of the instance
definitions are identical: typically for every transformer (using
`StateT s m` as an example) it becomes a matter of:

* Possibly unwrap the transformer from a monadic value to get the
  lower monad (e.g. `StateT s m a -> m (a,s)`);

* Possibly add internal values (e.g. `m a -> m (a,s)`);

* Wrap the lower monad from the result of the computation back up into
  the transformer (e.g. `m (a,s) -> StateT s m a`).

The solution
------------

Ideally, instead we'd have something along the lines of (simplified):

```haskell

class (Monad m) => MonadBase m where
  type BaseMonad m :: * -> *

  liftBase :: BaseMonad m a -> m a

class (MonadBase m) => MonadLevel m where

  type LowerMonad m :: * -> *

  type InnerValue m a :: *

  -- A continuation-based approach for how to lift/lower a monadic value.
  wrap :: (    (m a -> LowerMonad m (InnerValue m a)             -- unwrap
            -> (LowerMonad m a -> LowerMonad m (InnerValue m a)) -- addInternal
            -> LowerMonad m (InnerValue m a)
          )
          -> m a
```

With these two classes, we could then use Advanced Type Hackery (TM)
to let us instead just specify instances for the transformers/monads
that *do* have direct implementations for a typeclass, and then have
the rest defined for us!

It turns out that this approach is even powerful enough to make
`liftBase` redundant, and it isn't limited to just lifting a monad but
can instead be used for arbitrary functions.

Advantages
----------

* Minimal specification required for adding new typeclasses: just
  specify the instances for monads that satisfy it, and then use the
  provided machinery to lift/lower methods to other transformers in
  the monadic stack.

* Works even for polyvariadic functions.

* Still allows specifying whether certain transformers do _not_ allow
  some constraints to pass through (e.g. `ContT` does not allow access
  to a `WriterT`).

Disadvantages
-------------

* Requires a _lot_ of GHC extensions.

* Requires usage of proxies when lifting/lowering typeclass methods.

* Large usage of associated types means type errors can be difficult
  to decipher.

* Assumes that monad transformers like `StateT` can allow any
  constraint through.

* Due to usage of closed type-families, it is not possible to add
  extra instances to typeclasses (i.e. it is not possible to use a
  custom `State` monad/monad-transformer with
  `Control.Monad.Levels.State`).

* Currently un-benchmarked; as such, it's not known how much of a
  performance penalty this approach takes.

* Lowering polyvariadic functions requires specifying the type of the
  function using a specific grammar (though the common `m a -> m a`
  case is pre-defined).
