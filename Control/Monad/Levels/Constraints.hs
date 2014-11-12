{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances,
             KindSignatures, MultiParamTypeClasses, PolyKinds, RankNTypes,
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
       , liftSat
         -- * Re-exported for convenience
       , Proxy(..)
       ) where

import Control.Monad.Levels.ConstraintPassing
import Control.Monad.Levels.Definitions

import Data.Proxy (Proxy (..))
import GHC.Exts   (Constraint)

-- -----------------------------------------------------------------------------

data Nat = Zero | Suc Nat

class (MonadTower m) => SatisfyConstraint_ (n :: Nat) (c :: (* -> *) -> Constraint) m where

  _liftSat :: Proxy n -> Proxy c -> SatMonad c m a -> m a

instance (MonadTower m, c m, m ~ SatMonad c m) => SatisfyConstraint_ Zero c m where

  _liftSat _ _ m = m

instance (ConstraintCanPassThrough c m, SatisfyConstraint_ n c (LowerMonad m)
         , SatMonad c m ~ SatMonad c (LowerMonad m))
         => SatisfyConstraint_ (Suc n) c m where

  _liftSat _ c m = wrap (\ _unwrap addI -> addI (_liftSat (Proxy :: Proxy n) c m))

type SatisfyConstraint c m = ( SatisfyConstraint_ (FindSatisfied c m) c m
                             , c (SatMonad c m)
                             -- Best current way of stating that the
                             -- satisfying monad is a lower level of
                             -- the specified one.
                             , BaseMonad (SatMonad c m) ~ BaseMonad m)

liftSat :: forall c m a. (SatisfyConstraint c m) =>
         Proxy (c :: (* -> *) -> Constraint) -> SatMonad c m a -> m a
liftSat  p m = _liftSat (Proxy :: Proxy (FindSatisfied c m)) p m

-- -----------------------------------------------------------------------------

type family ConstraintSatisfied (c :: (* -> *) -> Constraint) (m :: * -> *) :: Bool

type TrySatisfy (c :: (* -> *) -> Constraint) (m :: (* -> *)) = TrySatisfy' c (BaseMonad m) m

type family TrySatisfy' (c :: (* -> *) -> Constraint) (b :: (* -> *)) (m :: (* -> *)) :: [(Bool, * -> *)] where
  TrySatisfy' c b b = '(ConstraintSatisfied c b, b) ': '[]
  TrySatisfy' c b m = '(ConstraintSatisfied c m, m) ': TrySatisfy' c b (LowerMonad m)

type family FindTrue (bms :: [(Bool, * -> *)]) :: Nat where
  FindTrue ('(True,  m) ': t) = Zero
  FindTrue ('(False, m) ': t) = Suc (FindTrue t)

type FindSatisfied (c :: (* -> *) -> Constraint) (m :: * -> *) = FindTrue (TrySatisfy c m)

type family FindSat (bms :: [(Bool, k)]) :: k where
  FindSat ('(True,  m) ': t) = m
  FindSat ('(False, m) ': t) = FindSat t

-- | The Monad in the tower that satisfies the provided constraint.
type SatMonad (c :: (* -> *) -> Constraint) (m :: * -> *) = FindSat (TrySatisfy c m)

type ValueAt (c :: (* -> *) -> Constraint) (m :: (* -> *)) a = ValueAt' c (BaseMonad m) m a

type family ValueAt' (c :: (* -> *) -> Constraint) (b :: (* -> *)) (m :: (* -> *)) a :: [(Bool, *)] where
  ValueAt' c b b a = '(ConstraintSatisfied c b, a) ': ' []
  ValueAt' c b m a = '(ConstraintSatisfied c m, a) ': ValueAt' c b (LowerMonad m) (InnerValue m a)

type SatValue (c :: (* -> *) -> Constraint) (m :: * -> *) a = FindSat (ValueAt c m a)

-- -----------------------------------------------------------------------------

-- | Class representing arguments/parameters for lower-able variadic
--   functions.
--
--   An argument is either:
--
--       * A constant value 'Const'
--
--       * A value in the specified monad 'MonadicValue'
--
--       * A function from a constant to an existing 'VariadicArg' instance 'Func'.
class VariadicArg v where

  -- | The type that the variadic guard corresponds to within the
  --   monad @(m a)@.
  type VariadicType v (m :: * -> *) a

  lowerVArg :: (MonadLevel m) => Proxy v
                              -> VariadicType v m a
                              -> Unwrapper m a (VariadicType v (LowerMonad m) (InnerValue m a))

-- | A constant type that does not depend upon the current monadic
--   context.  That is, @Const b@ corresponds to just @b@.
data Const (b :: *)

instance VariadicArg (Const b) where
  type VariadicType (Const b) m a = b

  lowerVArg _ b _ _ = b

-- | Corresponds to @m a@.
data MonadicValue

instance VariadicArg MonadicValue where
  type VariadicType MonadicValue m a = m a

  lowerVArg _ m unwrap _ = unwrap m

-- | Represents the function @a -> b@.
data Func (a :: *) (b :: *)

instance (VariadicArg va) => VariadicArg (Func b va) where
  type VariadicType (Func b va) m a = b -> VariadicType va m a

  lowerVArg _ f unwrap addI
    = (\ v -> lowerVArg (Proxy :: Proxy va) v unwrap addI)
      . f

-- | A function composed of variadic arguments that produces a value
--   of type @m a@.
class VariadicFunction f where

  -- | The function (that produces a value of type @t@) that this
  --   instance corresponds to.
  type VarFunction f (m :: * -> *) a

  applyVFn :: (MonadLevel m) => Proxy f -> Proxy m -> Proxy a
              -> Unwrapper m a (VarFunctionLower f m a)
              -> VarFunction f m a

type VarFunctionLower f (m :: * -> *) a = VarFunction f (LowerMonad m) (InnerValue m a)

data MkVarFn va

instance (VariadicArg va) => VariadicFunction (MkVarFn va) where
  type VarFunction (MkVarFn va) m a = VariadicType va m a -> m a

  applyVFn _ f va = wrap (\ unwrap addI -> f unwrap addI (lowerVArg (Proxy :: Proxy va) va unwrap addI))

instance (VariadicArg va, VariadicFunction vf) => VariadicFunction (Func va vf) where
  type VarFunction  (Func va vf) m a = (VariadicType va m a) -> VarFunction vf m a

  applyVFn _ f va = applyVFn (Proxy :: Proxy vf)
                             (\ unwrap addI -> f unwrap addI (lowerVArg (Proxy :: Proxy va) va unwrap addI))
