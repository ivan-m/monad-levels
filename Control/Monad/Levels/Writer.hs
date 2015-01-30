{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances,
             MultiParamTypeClasses, ScopedTypeVariables, TupleSections,
             TypeFamilies #-}

{- |
   Module      : Control.Monad.Levels.Writer
   Description : Writer/logging monads
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : 3-Clause BSD-style
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Control.Monad.Levels.Writer
  ( writer
  , tell
  , HasWriter
  , listen
  , CanListen
  , ListenFn
  , pass
  , CanPass
  , PassFn
  , IsWriter
  ) where

import Control.Monad.Levels
import Control.Monad.Levels.Constraints

import Control.Arrow (second)
import Data.Monoid   (Endo (..), Monoid (..))

import qualified Control.Monad.Trans.RWS.Lazy      as LRWS
import qualified Control.Monad.Trans.RWS.Strict    as SRWS
import qualified Control.Monad.Trans.Writer.Lazy   as LW
import qualified Control.Monad.Trans.Writer.Strict as SW

-- -----------------------------------------------------------------------------

-- | The minimal definition needed for a monad providing a writer
--   environment.
class (Monoid w, MonadTower m) => IsWriter w m where

  _writer :: (a,w) -> m a

  _listen :: m a -> m (a,w)

  _pass :: m (a, w -> w) -> m a

instance (Monoid w, MonadTower m) => IsWriter w (LW.WriterT w m) where

  _writer = LW.writer

  _listen = LW.listen

  _pass = LW.pass

instance (Monoid w, MonadTower m) => IsWriter w (SW.WriterT w m) where

  _writer = SW.writer

  _listen = SW.listen

  _pass = SW.pass

instance (Monoid w, MonadTower m) => IsWriter w (LRWS.RWST r w s m) where

  _writer = LRWS.writer

  _listen = LRWS.listen

  _pass = LRWS.pass

instance (Monoid w, MonadTower m) => IsWriter w (SRWS.RWST r w s m) where

  _writer = SRWS.writer

  _listen = SRWS.listen

  _pass = SRWS.pass

instance (Monoid w) => ValidConstraint (IsWriter w) where
  type ConstraintSatisfied (IsWriter w) m = SameWriter w m

type family SameWriter w m where
  SameWriter w (LW.WriterT   w   m) = True
  SameWriter w (SW.WriterT   w   m) = True
  SameWriter w (LRWS.RWST  r w s m) = True
  SameWriter w (SRWS.RWST  r w s m) = True
  SameWriter w m                    = False

type HasWriter w m = (Monoid w, SatisfyConstraint (IsWriter w) m)

-- | Embed a simple writer action.
writer :: forall w m a. (HasWriter w m) => (a,w) -> m a
writer = liftSat (Proxy :: Proxy (IsWriter w)) . _writer

-- | An action that produces the output @w@.
tell :: (HasWriter w m) => w -> m ()
tell = writer . ((),)

type CanListen w m a = SatisfyConstraintF (IsWriter w) m a (ListenFn w)

type ListenFn w = Func MonadicValue (MkVarFnFrom (MonadicTuple w))

-- | Execute the action @m@ and add its output to the value of the
--   computation.
listen :: forall w m a. (CanListen w m a) => m a -> m (a,w)
listen = lowerSat c f m a _listen
  where
    c :: Proxy (IsWriter w)
    c = Proxy

    f :: Proxy (ListenFn w)
    f = Proxy

    m :: Proxy m
    m = Proxy

    a :: Proxy a
    a = Proxy

type CanPass w m a = SatisfyConstraintF (IsWriter w) m a (PassFn w)

type PassFn w = MkVarFn (MonadicTuple (Endo w))

-- | Execute the action @m@ (which returns a value and a function) and
--   returns the value, applying the function to the output.
pass :: forall w m a. (CanPass w m a) => m (a, w -> w) -> m a
pass = lowerSat c f m a (_pass . fmap (second appEndo)) . fmap (second Endo)
  where
    c :: Proxy (IsWriter w)
    c = Proxy

    f :: Proxy (PassFn w)
    f = Proxy

    m :: Proxy m
    m = Proxy

    a :: Proxy a
    a = Proxy
