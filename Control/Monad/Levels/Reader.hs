{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances,
             MultiParamTypeClasses, PolyKinds, RankNTypes, ScopedTypeVariables,
             TypeFamilies #-}

{- |
   Module      : Control.Monad.Levels.Reader
   Description : Dealing with Reader
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : 3-Clause BSD-style
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Control.Monad.Levels.Reader
  ( ReaderT(..)
  , ask
  , asks
  , reader
  , local
  , HasReader
  ) where

import Control.Monad.Levels
import Control.Monad.Levels.ConstraintPassing
import Control.Monad.Levels.Constraints
import Control.Monad.Levels.Definitions       (ValidConstraint (..))

import           Control.Monad.Trans.Cont       (ContT)
import           Control.Monad.Trans.List       (ListT)
import           Control.Monad.Trans.Reader     (ReaderT (..))
import qualified Control.Monad.Trans.Reader     as R
import qualified Control.Monad.Trans.RWS.Lazy   as LRWS
import qualified Control.Monad.Trans.RWS.Strict as SRWS
import           Data.Monoid

-- -----------------------------------------------------------------------------

class (MonadTower m) => IsReader r m where

  _local :: (r -> r) -> m a -> m a

  _reader :: (r -> a) -> m a

instance ValidConstraint (IsReader r) where
  type ConstraintSatisfied (IsReader r) m = SameReader r m

type family SameReader r m where
  SameReader r ((->) r)            = True
  SameReader r (ReaderT r m)       = True
  SameReader r (LRWS.RWST r w s m) = True
  SameReader r (SRWS.RWST r w s m) = True
  SameReader r m                   = False

type HasReader r m = SatisfyConstraint (IsReader r) m

local :: forall r m a. (HasReader r m) => (r -> r) -> m a -> m a
local = lowerFunction (Proxy :: Proxy (IsReader r)) . _local

reader :: forall r m a. (HasReader r m) => (r -> a) -> m a
reader = liftSat (Proxy :: Proxy (IsReader r)) . _reader

ask :: (HasReader r m) => m r
ask = reader id

asks :: (HasReader r m) => (r -> a) -> m a
asks = reader

-- -----------------------------------------------------------------------------

instance (MonadTower m) => IsReader r (ReaderT r m) where

  _local = R.local

  _reader = R.reader

instance IsReader r ((->) r) where

  _local f m = m . f

  _reader = id

instance (MonadTower m, Monoid w) => IsReader r (LRWS.RWST r w s m) where

  _local = LRWS.local

  _reader = LRWS.reader

instance (MonadTower m, Monoid w) => IsReader r (SRWS.RWST r w s m) where

  _local = SRWS.local

  _reader = SRWS.reader

-- -----------------------------------------------------------------------------
-- Dealing with ContT and ListT

instance (MonadTower m) => ConstraintPassThrough (IsReader r) (ContT c m) True
instance (MonadTower m) => ConstraintPassThrough (IsReader r) (ListT m) True
