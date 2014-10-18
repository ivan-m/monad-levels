{-# LANGUAGE ConstraintKinds, DataKinds, DefaultSignatures, DeriveFunctor,
             FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving,
             KindSignatures, MagicHash, MultiParamTypeClasses, PolyKinds,
             RankNTypes, ScopedTypeVariables, TypeFamilies, TypeOperators,
             UndecidableInstances #-}

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

-- -----------------------------------------------------------------------------

class (Applicative m, Monad m) => MonadTower_ m where

  type BaseMonad m :: * -> *
  type BaseMonad m = m

instance MonadTower_ []

class (MonadTower_ m, MonadTower_ (BaseMonad m), BaseMonad (BaseMonad m) ~ BaseMonad m, BaseMonad m ~ BaseMonad (BaseMonad m))
      => MonadTower m

instance (MonadTower_ m, MonadTower_ (BaseMonad m), BaseMonad (BaseMonad m) ~ BaseMonad m, BaseMonad m ~ BaseMonad (BaseMonad m))
         => MonadTower m

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

lift :: (MonadLevel m) => LowerMonad m a -> m a
lift m = wrap $ \ _unwrap addI -> addI m

-- -----------------------------------------------------------------------------

data Nat = Zero | Suc Nat

class (c (SatMonad_ n c m), ConstraintSatisfied c (SatMonad_ n c m) ~ True)
      => SatisfyConstraint_ (n :: Nat) (c :: (* -> *) -> Constraint) (m :: * -> *) where

  type SatMonad_ n c m :: * -> *

  _lower :: Proxy# n -> Proxy# c ->  SatMonad_ n c m a -> m a

instance (ConstraintSatisfied c m ~ True, c m) => SatisfyConstraint_ Zero c m where

  type SatMonad_ Zero c m = m

  _lower _ _ m = m

instance (MonadLevel m, SatisfyConstraint_ n c (LowerMonad m))
         => SatisfyConstraint_ (Suc n) c m where

  type SatMonad_ (Suc n) c m = SatMonad_ n c (LowerMonad m)

  _lower _ _ m = wrap (\ _unwrap addI -> addI (_lower (proxy# :: Proxy# n) (proxy# :: Proxy# c)  m))


type SatisfyConstraint c m = SatisfyConstraint_ (FindSatisfied c m) c m

type SatMonad c m = SatMonad_ (FindSatisfied c m) c m

lower :: forall c m a. (SatisfyConstraint c m) =>
         Proxy# (c :: (* -> *) -> Constraint) -> SatMonad c m a -> m a
lower = _lower (proxy# :: Proxy# (FindSatisfied c m))

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

type SatMonad' (c :: (* -> *) -> Constraint) (m :: * -> *) = FindSat (TrySatisfy c m)

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

-- -----------------------------------------------------------------------------

newtype ID m a = ID { unID :: m a }
  deriving (Eq, Ord, Show, Read, Functor, Applicative, Monad)

instance (MonadTower m) => MonadTower_ (ID m) where
  type BaseMonad (ID m) = BaseMonad m

instance (MonadTower m) => MonadLevel (ID m) where
  type LowerMonad (ID m) = m

  wrap f = ID (f unID id)
