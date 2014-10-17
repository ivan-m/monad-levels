{-# LANGUAGE TypeOperators #-}
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

class SatisfyConstraint_ (n :: Nat) (c :: (* -> *) -> Constraint) (m :: * -> *) where

  _lower :: Proxy c -> Proxy n -> (forall m'. (c m') => m' a) -> m a

instance (ConstraintSatisfied c m ~ True, c m) => SatisfyConstraint_ Zero c m where

  _lower _ _ m = m

instance (MonadLevel m, SatisfyConstraint_ n c (LowerMonad m))
         => SatisfyConstraint_ (Suc n) c m where

  _lower _ _ m = wrap (\ _unwrap addI -> addI (_lower (Proxy :: Proxy c) (Proxy :: Proxy n) m))


data Proxy (t :: k) = Proxy
             deriving (Show)

-- data DictMonadConstraint ::

type SatisfyConstraint c m = SatisfyConstraint_ (FindSatisfied c m) c m

lower :: forall c m a. (SatisfyConstraint c m) =>
         Proxy (c :: (* -> *) -> Constraint) -> (forall m'. (c m') => m' a) -> m a
lower p m = _lower p (Proxy :: Proxy (FindSatisfied c m)) m

type MonadConstraint c m = (Monad m, c m)

-- -----------------------------------------------------------------------------

type family FindLevel (c :: (* -> *) -> Constraint) (m :: (* -> *)) :: Nat

-- type instance (c m) => FindLevel c m = Zero

type family ConstraintSatisfied (c :: (* -> *) -> Constraint) (m :: * -> *) :: Bool

type TrySatisfy (c :: (* -> *) -> Constraint) (m :: (* -> *)) = TrySatisfy' c (BaseMonad m) m

type family TrySatisfy' (c :: (* -> *) -> Constraint) (b :: (* -> *)) (m :: (* -> *)) :: [Bool] where
  TrySatisfy' c b b = '[ ConstraintSatisfied c b ]
  -- Need this first in case of transformers that are not instance of MonadLevel
  TrySatisfy' c b (t m) = (ConstraintSatisfied c (t m)) ': TrySatisfy' c b m
  -- Still need this for newtype wrappers, etc.
  TrySatisfy' c b m = (ConstraintSatisfied c m) ': TrySatisfy' c b (LowerMonad m)

type family FindTrue (bs :: [Bool]) :: Nat where
  FindTrue (True  ': t) = Zero
  FindTrue (False ': t) = Suc (FindTrue t)

type FindSatisfied (c :: (* -> *) -> Constraint) (m :: * -> *) = FindTrue (TrySatisfy c m)

-- -----------------------------------------------------------------------------

type IsBaseMonad m = (MonadTower m, m ~ BaseMonad m)

type instance ConstraintSatisfied IsBaseMonad m = SameMonad (BaseMonad m) m

type family SameMonad m n where
  SameMonad m m = True
  SameMonad m n = False
