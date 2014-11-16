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
       ( HasTransformer
       , TransformedMonad
       , liftT
         -- * Exported for use with custom instances
       , IsTransformer
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
type HasTransformer t m = ( SatisfyConstraint (IsTransformer t) m
                          , MonadLevel (TransformedMonad t m)
                          , TransformedMonad t m ~ t (LowerMonad (TransformedMonad t m)))

-- | The sub-part of the monadic stack where the requested transformer
--   is on top.
type TransformedMonad t m = SatMonad (IsTransformer t) m

class (MonadLevel m, m ~ t (LowerMonad m), t (LowerMonad m) ~ m) => IsTransformer t m where
  _liftT :: m a -> m a
  _liftT m = m

instance (MonadLevel m, m ~ t (LowerMonad m), t (LowerMonad m) ~ m) => IsTransformer t m

type instance ConstraintSatisfied (IsTransformer (t :: (* -> *) -> * -> *)) (m :: * -> *) = SameTransformer t m

type family SameTransformer (t :: (* -> *) -> * -> *) (m :: * -> *) where
  SameTransformer t (t m) = True
  SameTransformer t m     = False

liftT :: (HasTransformer t m) => TransformedMonad t m a -> m a
liftT m = liftSat (Proxy :: Proxy (IsTransformer t)) (_liftT m)

-- -----------------------------------------------------------------------------
-- ContT and ListT instances

-- Note: RWS transformers aren't allowed for ContT and ListT as they
-- don't allow passing through of Writer manipulations.

instance (MonadLevel m) => ConstraintCanPassThrough (IsTransformer (LSt.StateT s)) (ContT r m)
instance (MonadLevel m) => ConstraintCanPassThrough (IsTransformer (LSt.StateT s)) (ListT m)

instance (MonadLevel m) => ConstraintCanPassThrough (IsTransformer (SSt.StateT s)) (ContT r m)
instance (MonadLevel m) => ConstraintCanPassThrough (IsTransformer (SSt.StateT s)) (ListT m)
