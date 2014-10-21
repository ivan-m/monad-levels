{-# LANGUAGE ConstraintKinds, FlexibleContexts, MagicHash,
             MultiParamTypeClasses, TypeFamilies #-}

{- |
   Module      : Control.Monad.Levels
   Description : Explicit level-based monad transformer stacks
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : 3-Clause BSD-style
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Control.Monad.Levels
       ( MonadTower_(..)
       , MonadTower
       , MonadLevel (..)
       , lift
       , HasBaseMonad
       , liftBase
       , BaseMonadOf
       , liftIO
       ) where

import Control.Monad.Levels.Constraints
import Control.Monad.Levels.Definitions

-- -----------------------------------------------------------------------------

lift :: (MonadLevel m) => LowerMonad m a -> m a
lift m = wrap $ \ _unwrap addI -> addI m

-- | Ideally, this alias would not be needed as every instance of
--   'MonadBase' should satisfy the required constraint.  However,
--   this is needed for technical reasons.
type HasBaseMonad m = SatisfyConstraint IsBaseMonad m

liftBase :: (HasBaseMonad m) => BaseMonad m a -> m a
liftBase m = lower (proxy# :: Proxy# IsBaseMonad) m
{-# INLINE liftBase #-}

type BaseMonadOf b m = (HasBaseMonad m, BaseMonad m ~ b, b ~ BaseMonad m)

-- | An alias defined for convenience with existing code.
liftIO :: (BaseMonadOf IO m) => IO a -> m a
liftIO = liftBase
