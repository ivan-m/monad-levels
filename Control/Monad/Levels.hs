{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts,
             MultiParamTypeClasses, PolyKinds, RankNTypes, ScopedTypeVariables,
             TypeFamilies, UndecidableInstances #-}

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
       , MonadLevel_(..)
       , MonadLevel
         -- * Basic level manipulation
       , lift
         -- ** Lifting from the base
       , HasBaseMonad
       , liftBase
       , BaseMonadOf
       , liftIO
         -- * Lifting from a specific transformer
       , HasTransformer
       , TransformedMonad
       , liftT
       ) where

import Control.Monad.Levels.Constraints
import Control.Monad.Levels.Definitions
import Control.Monad.Levels.Transformers

-- -----------------------------------------------------------------------------

lift :: (MonadLevel m) => LowerMonad m a -> m a
lift m = wrap $ \ _unwrap addI -> addI m

-- | Ideally, this alias would not be needed as every instance of
--   'MonadTower' should satisfy the required constraint.  However,
--   this is needed for technical reasons.
type HasBaseMonad m = SatisfyConstraint IsBaseMonad m

type instance ConstraintSatisfied IsBaseMonad m = SameMonad (BaseMonad m) m

type family SameMonad (m :: * -> *) (n :: * -> *) where
  SameMonad m m = True
  SameMonad m n = False

liftBase :: (HasBaseMonad m) => BaseMonad m a -> m a
liftBase m = liftSat (Proxy :: Proxy IsBaseMonad) m
{-# INLINE liftBase #-}

type BaseMonadOf b m = (HasBaseMonad m, BaseMonad m ~ b, b ~ BaseMonad m)

-- | An alias defined for convenience with existing code.
liftIO :: (BaseMonadOf IO m) => IO a -> m a
liftIO = liftBase
