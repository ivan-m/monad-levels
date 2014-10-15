{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances,
             KindSignatures, MultiParamTypeClasses, PolyKinds, RankNTypes,
             ScopedTypeVariables, TypeFamilies, UndecidableInstances #-}
{- |
   Module      : Control.Monad.Levels
   Description : Specific levls of monad transformers
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : 3-Clause BSD-style
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Control.Monad.Levels where

import Control.Applicative
import GHC.Exts            (Constraint)

-- -----------------------------------------------------------------------------

class (Applicative m, Monad m) => MonadTower m where

  type BaseMonad m :: * -> *

  liftBase :: BaseMonad m a -> m a

class (MonadTower m, MonadTower (LowerMonad m)
      , BaseMonad m ~ BaseMonad (LowerMonad m), BaseMonad (LowerMonad m) ~ BaseMonad m)
      => MonadLevel m where

  type LowerMonad m :: * -> *

  type InnerValue m a :: *

  wrap :: ( ( m a -> LowerMonad m (InnerValue m a))
              -> (LowerMonad m a -> LowerMonad m (InnerValue m a))
              -> LowerMonad m (InnerValue m a))
           -> m a

lift :: (MonadLevel m) => LowerMonad m a -> m a
lift m = wrap $ \ _unwrap addI -> addI m

data Nat = Zero | Suc Nat

class SatisfyConstraint (n :: Nat) (m :: * -> *) (c :: (* -> *) -> Constraint) where

  _lower :: Proxy c -> Proxy n -> (forall m'. (c m') => m' a) -> m a

instance (c m) => SatisfyConstraint Zero m c where

  _lower _ _ m = m

instance (MonadLevel m, SatisfyConstraint n (LowerMonad m) c)
         => SatisfyConstraint (Suc n) m c where

  _lower _ _ m = wrap (\ _unwrap addI -> addI (_lower (Proxy :: Proxy c) (Proxy :: Proxy n) m))

data Proxy t = Proxy
             deriving (Show)
