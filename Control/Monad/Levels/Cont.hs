{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts,
             MultiParamTypeClasses, ScopedTypeVariables, TypeFamilies,
             UndecidableInstances #-}
{- |
   Module      : Control.Monad.Levels.Cont
   Description : Continuation monad handling
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : 3-Clause BSD-style
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Control.Monad.Levels.Cont
  ( callCC
  , HasCont
  , IsCont
  ) where

import Control.Monad.Levels
import Control.Monad.Levels.Constraints

import           Control.Monad.Trans.Cont (ContT)
import qualified Control.Monad.Trans.Cont as C

-- -----------------------------------------------------------------------------

-- We don't use the Transformer constraint here because there's
-- problems with the @r@ when trying to resolve the constraint.

class (MonadLevel m) => IsCont m where
  -- Defined just to have it based upon the constraint
  _callCC :: CallCC m a b

instance (MonadTower m) => IsCont (ContT r m) where
  _callCC = C.callCC

instance ValidConstraint IsCont where
  type ConstraintSatisfied IsCont m = IsContT m

type family IsContT m where
  IsContT (ContT r m) = True
  IsContT m           = False

type HasCont m a b = SatisfyConstraintF IsCont m a (ContFn b)

type ContFn b = MkVarFn (Func (Func ValueOnly (MonadicOther b)) MonadicValue)

type CallCC m a b = VarFunction (ContFn b) m a

-- Not using CallCC here to avoid having to export it.
callCC :: forall m a b. (HasCont m a b) => ((a -> m b) -> m a) -> m a
callCC = lowerSat c vf m a _callCC
  where
    c :: Proxy IsCont
    c = Proxy

    vf :: Proxy (ContFn b)
    vf = Proxy

    m :: Proxy m
    m = Proxy

    a :: Proxy a
    a = Proxy
