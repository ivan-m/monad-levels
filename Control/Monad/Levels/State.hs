{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances,
             MultiParamTypeClasses, RankNTypes, ScopedTypeVariables,
             TypeFamilies #-}

{- |
   Module      : Control.Monad.Levels.State
   Description : Dealing with State
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : 3-Clause BSD-style
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Control.Monad.Levels.State where

import Control.Monad.Levels
import Control.Monad.Levels.Constraints

import           Control.Monad.Trans.Cont         (ContT)
import           Control.Monad.Trans.List         (ListT)
import qualified Control.Monad.Trans.RWS.Lazy     as LRWS
import qualified Control.Monad.Trans.RWS.Strict   as SRWS
import qualified Control.Monad.Trans.State.Lazy   as LSt
import qualified Control.Monad.Trans.State.Strict as SSt
import           Data.Monoid                      (Monoid)

-- -----------------------------------------------------------------------------

class (MonadTower m) => IsState s m where

  _state :: (s -> (a,s)) -> m a

instance ValidConstraint (IsState s) where
  type ConstraintSatisfied (IsState s) m = SameState s m

type family SameState s m where
  SameState s (LSt.StateT s m)    = True
  SameState s (SSt.StateT s m)    = True
  SameState s (LRWS.RWST r w s m) = True
  SameState s (SRWS.RWST r w s m) = True
  SameState s m                   = False

type HasState s m = SatisfyConstraint (IsState s) m

state :: forall m s a. (HasState s m) => (s -> (a,s)) -> m a
state = liftSat (Proxy :: Proxy (IsState s)) . _state

get :: (HasState s m) => m s
get = state (\s -> (s,s))

gets :: (HasState s m) => (s -> a) -> m a
gets f = state (\s -> (f s, s))

put :: (HasState s m) => s -> m ()
put s = state (const ((),s))

modify :: (HasState s m) => (s -> s) -> m ()
modify f = state (\ s -> ((), f s))

-- -----------------------------------------------------------------------------

instance (MonadTower m) => IsState s (LSt.StateT s m) where

  _state = LSt.state

instance (MonadTower m) => IsState s (SSt.StateT s m) where

  _state = SSt.state

instance (MonadTower m, Monoid w) => IsState s (LRWS.RWST r w s m) where

  _state = LRWS.state

instance (MonadTower m, Monoid w) => IsState s (SRWS.RWST r w s m) where

  _state = SRWS.state

-- -----------------------------------------------------------------------------
-- Dealing with ContT and ListT

instance (MonadTower m) => ConstraintPassThrough (IsState s) (ContT r m) True
instance (MonadTower m) => ConstraintPassThrough (IsState s) (ListT m) True
