{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts,
             MultiParamTypeClasses, ScopedTypeVariables, TypeFamilies #-}

{- |
   Module      : Control.Monad.Levels
   Description : Explicit level-based monad transformer stacks
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : MIT
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Control.Monad.Levels
       ( -- * Monadic stacks
         MonadTower_(..)
       , MonadTower
       , MonadLevel_(..)
       , MonadLevel
         -- * Helper types\/aliases
       , Unwrapper
       , LowerMonadValue
       , WithLower
       , CanUnwrap
       , CanUnwrapSelf
       , WithLowerC
         -- ** Manipulating internal values
       , AddInternalM(..)
       , CanAddInternalM
       , AddIM(..)
       , AddInternal(..)
       , CanAddInternal
       , AddI(..)
       , AddIdent(..)
       , GetInternal(..)
       , CanGetInternal
       , AddIG(..)
         -- * Basic level manipulation
       , lift
         -- ** Lifting from the base
       , IsBaseMonad
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

import Data.Constraint ((\\))

-- -----------------------------------------------------------------------------

lift :: forall m a. (MonadLevel m) => LowerMonad m a -> m a
lift lm = wrap a (\ _unwrap addI -> addInternalM addI lm) \\ proofInst m a
  where
    m :: Proxy m
    m = Proxy

    a :: Proxy a
    a = Proxy

-- | Ideally, this alias would not be needed as every instance of
--   'MonadTower' should satisfy the required constraint.  However,
--   this is needed for technical reasons.
type HasBaseMonad m = SatisfyConstraint IsBaseMonad m

liftBase :: (HasBaseMonad m) => BaseMonad m a -> m a
liftBase m = liftSat (Proxy :: Proxy IsBaseMonad) m
{-# INLINE liftBase #-}

type BaseMonadOf b m = (HasBaseMonad m, BaseMonad m ~ b, b ~ BaseMonad m)

-- | An alias defined for convenience with existing code.
liftIO :: (BaseMonadOf IO m) => IO a -> m a
liftIO = liftBase
