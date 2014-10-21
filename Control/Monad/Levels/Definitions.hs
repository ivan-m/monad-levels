{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances,
             TupleSections, TypeFamilies, UndecidableInstances #-}

{- |
   Module      : Control.Monad.Levels.Definitions
   Description : Specific levls of monad transformers
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : 3-Clause BSD-style
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Control.Monad.Levels.Definitions where

import Control.Applicative

import           Control.Monad.Trans.Cont       (ContT (..))
import qualified Control.Monad.Trans.State.Lazy as LSt
import           Data.Functor.Identity

-- -----------------------------------------------------------------------------

class (Applicative m, Monad m) => MonadTower_ m where

  type BaseMonad m :: * -> *
  type BaseMonad m = m

instance MonadTower_ []
instance MonadTower_ Maybe
instance MonadTower_ IO
instance MonadTower_ (Either e)
instance MonadTower_ ((->) r)

instance MonadTower_ Identity

instance (MonadTower m) => MonadTower_ (LSt.StateT s m) where
  type BaseMonad (LSt.StateT s m) = BaseMonad m

instance (MonadTower m) => MonadTower_ (ContT r m) where
  type BaseMonad (ContT r m) = BaseMonad m

type MonadTower m = ( MonadTower_ m, MonadTower_ (BaseMonad m)
                    , BaseMonad (BaseMonad m) ~ BaseMonad m
                    , BaseMonad m ~ BaseMonad (BaseMonad m))

-- -----------------------------------------------------------------------------

class (MonadTower m, MonadTower (LowerMonad m)
      , BaseMonad m ~ BaseMonad (LowerMonad m), BaseMonad (LowerMonad m) ~ BaseMonad m)
      => MonadLevel m where

  type LowerMonad m :: * -> *

  type InnerValue m a :: *
  type InnerValue m a = a

  type AllConstraintsThrough m :: Bool
  type AllConstraintsThrough m = True

  wrap :: ( ( m a -> LowerMonad m (InnerValue m a))
              -> (LowerMonad m a -> LowerMonad m (InnerValue m a))
              -> LowerMonad m (InnerValue m a))
           -> m a

instance (MonadTower m) => MonadLevel (LSt.StateT s m) where

  type LowerMonad (LSt.StateT s m) = m

  type InnerValue (LSt.StateT s m) a = (a,s)

  wrap f = LSt.StateT $ \ s -> f (`LSt.runStateT` s) (fmap (,s))

instance (MonadTower m) => MonadLevel (ContT r m) where

  type LowerMonad (ContT r m) = m

  type InnerValue (ContT r m) a = r

  type AllConstraintsThrough (ContT r m) = False

  wrap f = ContT $ \ cont -> f (`runContT` cont) (>>= cont)

-- -----------------------------------------------------------------------------

class (MonadTower m, m ~ BaseMonad m, BaseMonad m ~ m) => IsBaseMonad m where
  idBase :: m a -> m a
  idBase = id

instance (MonadTower m, m ~ BaseMonad m, BaseMonad m ~ m) => IsBaseMonad m
