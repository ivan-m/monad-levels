{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts,
             MultiParamTypeClasses, ScopedTypeVariables, TypeFamilies,
             UndecidableInstances #-}
{- |
   Module      : Control.Monad.Levels.Cont
   Description : Continuation monad handling
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : 3-Clause BSD-style
   Maintainer  : Ivan.Miljenovic@gmail.com

This module allows inclusion of 'ContT' into your monad stack so as to
represent continuation-passing style (CPS) computations.

Note that the behaviour of some monad transformers and how they deal
with continuations differs from how
<http://hackage.haskell.org/package/mtl mtl> handles them.  For
example, with a lazy state transformer, using this module results in
<http://hackage.haskell.org/package/transformers/docs/Control-Monad-Trans-State-Lazy.html#v:liftCallCC liftCallCC>,
whereas @mtl@ uses
<http://hackage.haskell.org/package/transformers/docs/Control-Monad-Trans-State-Lazy.html#v:liftCallCC-39- liftCallCC'>.

 -}
module Control.Monad.Levels.Cont
  ( callCC
  , ContT(..)
  , HasCont
  , IsCont
  , ContFn
  ) where

import Control.Monad.Levels
import Control.Monad.Levels.Constraints

import           Control.Monad.Trans.Cont (ContT (..))
import qualified Control.Monad.Trans.Cont as C

import Control.Monad.Trans.List (ListT)

-- -----------------------------------------------------------------------------

-- We don't use the Transformer constraint here because there's
-- problems with the @r@ when trying to resolve the constraint.

-- | A simple class just to match up with the 'ContT' monad
--   transformer.
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

-- | Represents monad stacks that can successfully pass 'callCC' down
--   to a 'ContT' transformer.
type HasCont m a b = SatisfyConstraintF IsCont m a (ContFn b)

-- | This corresponds to
--   <http://hackage.haskell.org/package/transformers/docs/Control-Monad-Signatures.html#t:CallCC CallCC>
--   in @transformers@.
type ContFn b = MkVarFn (Func (Func ValueOnly (MonadicOther b)) MonadicValue)

-- This is defined solely as an extra check on 'ContFn' matching the
-- type of 'C.callCC'.
type CallCC m a b = VarFunction (ContFn b) m a

-- Not using CallCC here to avoid having to export it.

-- | @callCC@ (call-with-current-continuation) calls a function with
--   the current continuation as its argument.
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

-- -----------------------------------------------------------------------------

instance (MonadTower m) => ConstraintPassThrough IsCont (ListT m) True
