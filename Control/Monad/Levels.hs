{-# LANGUAGE ConstraintKinds, DataKinds, DefaultSignatures, DeriveFunctor,
             FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving,
             KindSignatures, MagicHash, MultiParamTypeClasses, PolyKinds,
             RankNTypes, ScopedTypeVariables, TupleSections, TypeFamilies,
             TypeOperators, UndecidableInstances #-}

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
import GHC.Prim            (Proxy#, proxy#)

import qualified Control.Monad.Trans.State.Lazy as LSt

-- -----------------------------------------------------------------------------

class (Applicative m, Monad m) => MonadTower_ m where

  type BaseMonad m :: * -> *
  type BaseMonad m = m

instance MonadTower_ []

instance (MonadTower m) => MonadTower_ (LSt.StateT s m) where

  type BaseMonad (LSt.StateT s m) = BaseMonad m

type MonadTower m = ( MonadTower_ m, MonadTower_ (BaseMonad m)
                    , BaseMonad (BaseMonad m) ~ BaseMonad m
                    , BaseMonad m ~ BaseMonad (BaseMonad m))

class (MonadTower m, MonadTower (LowerMonad m)
      , BaseMonad m ~ BaseMonad (LowerMonad m), BaseMonad (LowerMonad m) ~ BaseMonad m)
      => MonadLevel m where

  type LowerMonad m :: * -> *

  type InnerValue m a :: *
  type InnerValue m a = a

  wrap :: ( ( m a -> LowerMonad m (InnerValue m a))
              -> (LowerMonad m a -> LowerMonad m (InnerValue m a))
              -> LowerMonad m (InnerValue m a))
           -> m a

instance (MonadTower m) => MonadLevel (LSt.StateT s m) where

  type LowerMonad (LSt.StateT s m) = m

  type InnerValue (LSt.StateT s m) a = (a,s)

  wrap f = LSt.StateT $ \ s -> f (`LSt.runStateT` s) (fmap (,s))

lift :: (MonadLevel m) => LowerMonad m a -> m a
lift m = wrap $ \ _unwrap addI -> addI m

-- -----------------------------------------------------------------------------

data Nat = Zero | Suc Nat

class SatisfyConstraint_ (n :: Nat) (c :: (* -> *) -> Constraint) (m :: * -> *) where

  _lower :: Proxy# n -> Proxy# c ->  SatMonad c m a -> m a

instance (c m, m ~ SatMonad c m) => SatisfyConstraint_ Zero c m where

  _lower _ _ m = m

instance (MonadLevel m, SatisfyConstraint_ n c (LowerMonad m), SatMonad c m ~ SatMonad c (LowerMonad m))
         => SatisfyConstraint_ (Suc n) c m where

  _lower _ c m = wrap (\ _unwrap addI -> addI (_lower (proxy# :: Proxy# n) c m))


type SatisfyConstraint c m = ( SatisfyConstraint_ (FindSatisfied c m) c m
                             , c (SatMonad c m))

lower :: forall c m a. (SatisfyConstraint c m) =>
         Proxy# (c :: (* -> *) -> Constraint) -> SatMonad c m a -> m a
lower  p m = _lower (proxy# :: Proxy# (FindSatisfied c m)) p (m :: SatMonad c m a)

type MonadConstraint c m = (Monad m, c m)

-- -----------------------------------------------------------------------------

type family FindLevel (c :: (* -> *) -> Constraint) (m :: (* -> *)) :: Nat

type family ConstraintSatisfied (c :: (* -> *) -> Constraint) (m :: * -> *) :: Bool

type TrySatisfy (c :: (* -> *) -> Constraint) (m :: (* -> *)) = TrySatisfy' c (BaseMonad m) m

type family TrySatisfy' (c :: (* -> *) -> Constraint) (b :: (* -> *)) (m :: (* -> *)) :: [(Bool, * -> *)] where
  TrySatisfy' c b b = '[ '(ConstraintSatisfied c b, b) ]
  -- Need this first in case of transformers that are not instance of MonadLevel
  TrySatisfy' c b (t m) = '(ConstraintSatisfied c (t m), t m) ': TrySatisfy' c b m
  -- Still need this for newtype wrappers, etc.
  TrySatisfy' c b m = '(ConstraintSatisfied c m, m) ': TrySatisfy' c b (LowerMonad m)

type family FindTrue (bms :: [(Bool, * -> *)]) :: Nat where
  FindTrue ('(True,  m) ': t) = Zero
  FindTrue ('(False, m) ': t) = Suc (FindTrue t)

type FindSatisfied (c :: (* -> *) -> Constraint) (m :: * -> *) = FindTrue (TrySatisfy c m)

type family FindSat (bms :: [(Bool, * -> *)]) :: * -> * where
  FindSat ('(True,  m) ': t) = m
  FindSat ('(False, m) ': t) = FindSat t

-- | The Monad in the tower that satisfies the provided constraint.
type SatMonad (c :: (* -> *) -> Constraint) (m :: * -> *) = FindSat (TrySatisfy c m)

-- -----------------------------------------------------------------------------

class (MonadTower m, m ~ BaseMonad m, BaseMonad m ~ m) => IsBaseMonad m where
  idBase :: m a -> m a
  idBase = id

instance (MonadTower m, m ~ BaseMonad m, BaseMonad m ~ m) => IsBaseMonad m

type instance ConstraintSatisfied IsBaseMonad m = SameMonad (BaseMonad m) m

type family SameMonad m n where
  SameMonad m m = True
  SameMonad m n = False

class (MonadTower m, MonadTower n) => IsSameMonad m n
instance (MonadTower m, MonadTower n, m ~ n) => IsSameMonad m n

type instance ConstraintSatisfied (IsSameMonad m) n = SameMonad m n

type HasBaseMonad m = (MonadTower m, SatisfyConstraint IsBaseMonad m, SatMonad IsBaseMonad m ~ BaseMonad m)

liftBase :: (HasBaseMonad m) => BaseMonad m a -> m a
liftBase m = lower (proxy# :: Proxy# IsBaseMonad) m
{-# INLINE liftBase #-}

type IOBase m = (HasBaseMonad m, BaseMonad m ~ IO)

liftIO :: (IOBase m) => IO a -> m a
liftIO = liftBase

-- -----------------------------------------------------------------------------

class (MonadTower m) => HasState_ s m where

  _state :: (s -> (a,s)) -> m a

  _get :: m s
  _get = _state (\s -> (s,s))
  {-# INLINE _get #-}

  _put :: s -> m ()
  _put s = _state (const ((),s))
  {-# INLINE _put #-}

instance (MonadTower m) => HasState_ s (LSt.StateT s m) where

  _state = LSt.state

  _get = LSt.get

  _put = LSt.put

type instance ConstraintSatisfied (HasState_ s) m = SameState s m

type family SameState s m where
  SameState s (LSt.StateT s m) = True
  SameState s m                = False

type HasState s m = ( MonadTower_ m
                    , SatisfyConstraint (HasState_ s) m
                    , HasState_ s (SatMonad (HasState_ s) m))

state :: forall m s a. (HasState s m) => (s -> (a,s)) -> m a
state = lower (proxy# :: Proxy# (HasState_ s)) . _state

get :: (HasState s m) => m s
get = state (\s -> (s,s))

modify :: (HasState s m) => (s -> s) -> m ()
modify f = state (\ s -> ((), f s))

-- -----------------------------------------------------------------------------

newtype ID m a = ID { unID :: m a }
  deriving (Eq, Ord, Show, Read, Functor, Applicative, Monad)

instance (MonadTower m) => MonadTower_ (ID m) where
  type BaseMonad (ID m) = BaseMonad m

instance (MonadTower m) => MonadLevel (ID m) where
  type LowerMonad (ID m) = m

  wrap f = ID (f unID id)
