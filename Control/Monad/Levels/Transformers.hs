{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances,
             MultiParamTypeClasses, ScopedTypeVariables, TypeFamilies,
             UndecidableInstances #-}

{- |
   Module      : Control.Monad.Levels.Transformers
   Description : Lower down to a specific transformer
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : MIT
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Control.Monad.Levels.Transformers
       ( HasTransformer
       , TransformedMonad
       , liftT
         -- * Exported for use with custom instances
       , IsTransformer
       ) where

import Control.Monad.Levels.Constraints
import Control.Monad.Levels.Definitions

-- -----------------------------------------------------------------------------

type HasTransformer t m = ( SatisfyConstraint (IsTransformer t) m
                          , MonadLevel (TransformedMonad t m)
                          , TransformedMonad t m ~ t (LowerMonad (TransformedMonad t m)))

-- | The sub-part of the monadic stack where the requested transformer
--   is on top.
type TransformedMonad t m = SatMonad (IsTransformer t) m

class (MonadLevel m, m ~ t (LowerMonad m), t (LowerMonad m) ~ m) => IsTransformer t m

instance (MonadLevel m, m ~ t (LowerMonad m), t (LowerMonad m) ~ m) => IsTransformer t m

instance ValidConstraint (IsTransformer t) where
  type ConstraintSatisfied (IsTransformer t) m = SameTransformer t m

type family SameTransformer (t :: (* -> *) -> * -> *) (m :: * -> *) where
  SameTransformer t (t m) = True
  SameTransformer t m     = False

liftT :: (HasTransformer t m) => TransformedMonad t m a -> m a
liftT m = liftSat (Proxy :: Proxy (IsTransformer t)) m

-- -----------------------------------------------------------------------------

instance (MonadLevel m) => ConstraintPassThrough (IsTransformer t) m True
