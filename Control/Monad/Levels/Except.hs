{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances,
             MultiParamTypeClasses, ScopedTypeVariables, TypeFamilies #-}

-- unsafeCoerceConstraint is used to prevent the need for a complex
-- induction proof (which I'm not sure can actually be achieved).
{-# LANGUAGE Trustworthy #-}

{- |
   Module      : Control.Monad.Levels.Except
   Description : Error-handling monadic computations
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : 3-Clause BSD-style
   Maintainer  : Ivan.Miljenovic@gmail.com

Computations which may fail or throw exceptions.

 -}
module Control.Monad.Levels.Except
  ( throwError
  , catchError
  , ExceptT(..)
  , HasError
  , IsError
  ) where

import Control.Monad.Levels
import Control.Monad.Levels.Constraints

import Data.Constraint

import           Control.Exception          (IOException, catch)
import           Control.Monad.Trans.Except (ExceptT (..))
import qualified Control.Monad.Trans.Except as E

-- -----------------------------------------------------------------------------

-- | Constraint for monads that can throw and handle exceptions.
class (MonadTower m) => IsError e m where

  _throwError :: e -> m a

  _catchError :: VarFunction (CatchFn e) m a

instance IsError IOException IO where

  _throwError = ioError

  _catchError = catch

instance IsError e (Either e) where

  _throwError = Left

  _catchError e f = either f Right e

instance (MonadTower m) => IsError e (ExceptT e m) where

  _throwError = E.throwE

  _catchError = E.catchE

instance ValidConstraint (IsError e) where
  type ConstraintSatisfied (IsError e) m = SameError e m

type family SameError e m where
  SameError IOException IO            = True
  SameError e           (Either e)    = True
  SameError e           (ExceptT e m) = True
  SameError e           m             = False

-- | A monad stack that can throw and handle exceptions of type @e@.
type HasError e m = SatisfyConstraint (IsError e) m

-- | Begin exception processing.
throwError :: forall e m a. (HasError e m) => e -> m a
throwError = liftSat (Proxy :: Proxy (IsError e)) . _throwError

type CatchFn e = Func MonadicValue (MkVarFn (Func (Const e) MonadicValue))

-- | Handle exception processing.
catchError :: forall e m a. (HasError e m) => m a -> (e -> m a) -> m a
catchError = lowerSat' c vf m a (Sub Dict) _catchError
  where
    c :: Proxy (IsError e)
    c = Proxy

    vf :: Proxy (CatchFn e)
    vf = Proxy

    m :: Proxy m
    m = Proxy

    a :: Proxy a
    a = Proxy
