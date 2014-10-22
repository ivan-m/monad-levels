{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances,
             MagicHash, MultiParamTypeClasses, ScopedTypeVariables, TypeFamilies
             #-}

{- |
   Module      : Control.Monad.Levels.Transformers
   Description : Lower down to a specific transformer
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : 3-Clause BSD-style
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Control.Monad.Levels.Transformers
       ( CanLiftTransformer
       , TransformedMonad
       , liftT
         -- * Exported for use with custom instances
       , HasTransformer_
       ) where

import Control.Monad.Levels.Constraints
import Control.Monad.Levels.Definitions

-- -----------------------------------------------------------------------------

-- | Unlike 'HasBaseMonad', this is not a universal constraint
--   applicable to all 'MonadLevel' instances, as otherwise it can be
--   used to bypass the lack of an allowed constraint.
type CanLiftTransformer t m = ( SatisfyConstraint (HasTransformer_ t) m
                              , MonadLevel (TransformedMonad t m)
                              , TransformedMonad t m ~ t (LowerMonad (TransformedMonad t m)))

-- | The sub-part of the monadic stack where the requested transformer
--   is on top.
type TransformedMonad t m = SatMonad (HasTransformer_ t) m

class (MonadLevel m, m ~ t (LowerMonad m), t (LowerMonad m) ~ m) => HasTransformer_ t m where
  _liftT :: m a -> m a
  _liftT m = m

instance (MonadLevel m, m ~ t (LowerMonad m), t (LowerMonad m) ~ m) => HasTransformer_ t m

type instance ConstraintSatisfied (HasTransformer_ (t :: (* -> *) -> * -> *)) (m :: * -> *) = IsTransformer t m

type family IsTransformer (t :: (* -> *) -> * -> *) (m :: * -> *) where
  IsTransformer t (t m) = True
  IsTransformer t m     = False

liftT :: (CanLiftTransformer t m) => TransformedMonad t m a -> m a
liftT m = lower (proxy# :: Proxy# (HasTransformer_ t)) (_liftT m)
