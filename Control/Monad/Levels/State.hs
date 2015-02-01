{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances,
             MultiParamTypeClasses, ScopedTypeVariables, TypeFamilies #-}

{- |
   Module      : Control.Monad.Levels.State
   Description : Dealing with State
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : 3-Clause BSD-style
   Maintainer  : Ivan.Miljenovic@gmail.com

Monad environments for stateful computations.

 -}
module Control.Monad.Levels.State
  ( state
  , get
  , gets
  , put
  , modify
  , modify'
  , HasState
  , IsState
  ) where

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

-- | The minimal definition needed for a monad providing a stateful
--   environment.
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

-- | A monad stack containing a stateful environment of type @s@.
type HasState s m = SatisfyConstraint (IsState s) m

-- | Embed a simple state action into the monad stack.
state :: forall m s a. (HasState s m) => (s -> (a,s)) -> m a
state = liftSat (Proxy :: Proxy (IsState s)) . _state

-- | Obtain the state environment.
get :: (HasState s m) => m s
get = state (\s -> (s,s))

-- | Apply a function to the stateful environment.  Equivalent to
--   @fmap f 'get'@.
gets :: (HasState s m) => (s -> a) -> m a
gets f = state (\s -> (f s, s))

-- | Replace the stateful environment.
put :: (HasState s m) => s -> m ()
put s = state (const ((),s))

-- | Map the old state to a new state, and discard the old one.
--   Equivalent to @'gets' f >>= 'put'@.
modify :: (HasState s m) => (s -> s) -> m ()
modify f = state (\ s -> ((), f s))

-- | A variant of 'modify' in which the computation is strict in the
--   new state.
modify' :: (HasState s m) => (s -> s) -> m ()
modify' f = state (\ s -> let s' = f s in s' `seq` ((), s'))

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
