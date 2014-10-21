{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances,
             MagicHash, MultiParamTypeClasses, RankNTypes, ScopedTypeVariables,
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
import Control.Monad.Levels.ConstraintPassing
import Control.Monad.Levels.Constraints

import           Control.Monad.Trans.Cont       (ContT (..))
import qualified Control.Monad.Trans.State.Lazy as LSt

-- -----------------------------------------------------------------------------

class (MonadTower m) => HasState_ s m where

  _state :: (s -> (a,s)) -> m a

instance (MonadTower m) => HasState_ s (LSt.StateT s m) where

  _state = LSt.state

type instance ConstraintSatisfied (HasState_ s) m = SameState s m

type family SameState s m where
  SameState s (LSt.StateT s m) = True
  SameState s m                = False

type HasState s m = SatisfyConstraint (HasState_ s) m

state :: forall m s a. (HasState s m) => (s -> (a,s)) -> m a
state = lower (proxy# :: Proxy# (HasState_ s)) . _state

get :: (HasState s m) => m s
get = state (\s -> (s,s))

modify :: (HasState s m) => (s -> s) -> m ()
modify f = state (\ s -> ((), f s))

instance (MonadLevel m) => ConstraintCanPassThrough (HasState_ s) (ContT r m)
