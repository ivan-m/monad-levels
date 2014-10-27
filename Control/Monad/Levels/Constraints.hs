{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances,
             KindSignatures, MagicHash, MultiParamTypeClasses, RankNTypes,
             ScopedTypeVariables, TypeFamilies, TypeOperators,
             UndecidableInstances #-}

{- |
   Module      : Control.Monad.Levels.Constraints
   Description : A Level-based approach to constraints
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : 3-Clause BSD-style
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Control.Monad.Levels.Constraints
       ( SatisfyConstraint
       , ConstraintSatisfied
       , SatMonad
       , lower
         -- * Re-exported for convenience
       , Proxy#
       , proxy#
       ) where

import Control.Monad.Levels.ConstraintPassing
import Control.Monad.Levels.Definitions

import GHC.Exts (Constraint)
import GHC.Prim (Proxy#, proxy#)

-- -----------------------------------------------------------------------------

data Nat = Zero | Suc Nat

class (MonadTower m) => SatisfyConstraint_ (n :: Nat) (c :: (* -> *) -> Constraint) m where

  _lower :: Proxy# n -> Proxy# c -> SatMonad c m a -> m a

instance (MonadTower m, c m, m ~ SatMonad c m) => SatisfyConstraint_ Zero c m where

  _lower _ _ m = m

instance (ConstraintCanPassThrough c m, SatisfyConstraint_ n c (LowerMonad m)
         , SatMonad c m ~ SatMonad c (LowerMonad m))
         => SatisfyConstraint_ (Suc n) c m where

  _lower _ c m = wrap (\ _unwrap addI -> addI (_lower (proxy# :: Proxy# n) c m))


type SatisfyConstraint c m = ( SatisfyConstraint_ (FindSatisfied c m) c m
                             , c (SatMonad c m)
                             -- Best current way of stating that the
                             -- satisfying monad is a lower level of
                             -- the specified one.
                             , BaseMonad (SatMonad c m) ~ BaseMonad m)

lower :: forall c m a. (SatisfyConstraint c m) =>
         Proxy# (c :: (* -> *) -> Constraint) -> SatMonad c m a -> m a
lower  p m = _lower (proxy# :: Proxy# (FindSatisfied c m)) p (m :: SatMonad c m a)

-- -----------------------------------------------------------------------------

type family ConstraintSatisfied (c :: (* -> *) -> Constraint) (m :: * -> *) :: Bool

type TrySatisfy (c :: (* -> *) -> Constraint) (m :: (* -> *)) = TrySatisfy' c (BaseMonad m) m

type family TrySatisfy' (c :: (* -> *) -> Constraint) (b :: (* -> *)) (m :: (* -> *)) :: [(Bool, * -> *)] where
  TrySatisfy' c b b = '[ '(ConstraintSatisfied c b, b) ]
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
