{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances,
             MultiParamTypeClasses, ScopedTypeVariables, TypeFamilies #-}

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

import Control.Monad.Levels.ConstraintPassing
import Control.Monad.Levels.Constraints
import Control.Monad.Levels.Definitions

import           Control.Monad.Trans.Cont         (ContT)
import           Control.Monad.Trans.List         (ListT)
import qualified Control.Monad.Trans.State.Lazy   as LSt
import qualified Control.Monad.Trans.State.Strict as SSt

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
liftT m = lower (Proxy :: Proxy (HasTransformer_ t)) (_liftT m)

-- -----------------------------------------------------------------------------
-- ContT and ListT instances

-- Note: RWS transformers aren't allowed for ContT and ListT as they
-- don't allow passing through of Writer manipulations.

instance (MonadLevel m) => ConstraintCanPassThrough (HasTransformer_ (LSt.StateT s)) (ContT r m)
instance (MonadLevel m) => ConstraintCanPassThrough (HasTransformer_ (LSt.StateT s)) (ListT m)

instance (MonadLevel m) => ConstraintCanPassThrough (HasTransformer_ (SSt.StateT s)) (ContT r m)
instance (MonadLevel m) => ConstraintCanPassThrough (HasTransformer_ (SSt.StateT s)) (ListT m)
