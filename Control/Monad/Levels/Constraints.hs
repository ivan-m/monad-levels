{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances,
             KindSignatures, MultiParamTypeClasses, RankNTypes,
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
       , Proxy(..)
       ) where

import Control.Monad.Levels.ConstraintPassing
import Control.Monad.Levels.Definitions

import Data.Proxy (Proxy (..))
import GHC.Exts   (Constraint)

-- -----------------------------------------------------------------------------

data Nat = Zero | Suc Nat

class (MonadTower m) => SatisfyConstraint_ (n :: Nat) (c :: (* -> *) -> Constraint) m where

  _lower :: Proxy n -> Proxy c -> SatMonad c m a -> m a

instance (MonadTower m, c m, m ~ SatMonad c m) => SatisfyConstraint_ Zero c m where

  _lower _ _ m = m

instance (ConstraintCanPassThrough c m, SatisfyConstraint_ n c (LowerMonad m)
         , SatMonad c m ~ SatMonad c (LowerMonad m))
         => SatisfyConstraint_ (Suc n) c m where

  _lower _ c m = wrap (\ _unwrap addI -> addI (_lower (Proxy :: Proxy n) c m))


type SatisfyConstraint c m = ( SatisfyConstraint_ (FindSatisfied c m) c m
                             , c (SatMonad c m)
                             -- Best current way of stating that the
                             -- satisfying monad is a lower level of
                             -- the specified one.
                             , BaseMonad (SatMonad c m) ~ BaseMonad m)

lower :: forall c m a. (SatisfyConstraint c m) =>
         Proxy (c :: (* -> *) -> Constraint) -> SatMonad c m a -> m a
lower  p m = _lower (Proxy :: Proxy (FindSatisfied c m)) p (m :: SatMonad c m a)

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
data Const b

instance VariadicArg (Const b) where
  type VariadicType (Const b) m a = b

  lowerVArg _ b _ _ = b

-- | Corresponds to @m a@.
data MonadicValue

instance VariadicArg MonadicValue where
  type VariadicType MonadicValue m a = m a

  lowerVArg _ m unwrap _ = unwrap m

-- | Represents the function @a -> b@.
data Func a b

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
  type VarFnType f (m :: * -> *) a t

  -- | This is used to distinguish between instances based upon
  --   'AsIs' and 'AddInternal', as they have different intermediary result
  --   types (i.e. they produce functions that result in @m
  --   (ResultType f m a)@.
  type ResultType f (m :: * -> *) a

  applyVFn :: (MonadLevel m) => Proxy f
              -> Unwrapper m a (VarFnTypeLower f m a (LowerMonad m (ResultType f m a)))
              -> VarFunction f m a

type VarFnTypeLower f (m :: * -> *) a t = VarFnType f (LowerMonad m) (InnerValue m a) t

type VarFunction f m a = VarFnType f m a (m a)

type VarFunctionResult f m a = VarFnType f m a (m (ResultType f m a))

-- | For use with functions that deal primarily with lowering monadic
--   values and then manipulate them rather than creating new values.
--   At each stage during the transformer stack, the result is of the
--   form @LowerMonad m (InnerValue m a)@.
data AsIs va

instance (VariadicArg va) => VariadicFunction (AsIs va) where
  type VarFnType (AsIs va) m a t = VariadicType va m a -> t
  type ResultType (AsIs va) m a = InnerValue m a

  applyVFn _ f va = wrap (\ unwrap addI -> f unwrap addI (lowerVArg (Proxy :: Proxy va) va unwrap addI))

-- | For use with functions that produce a monadic value at the level
--   of the satisfying monad and thus need to have internal state
--   added before being lifted to the next level of the transformer
--   stack.
data AddInternal va

instance (VariadicArg va) => VariadicFunction (AddInternal va) where
  type VarFnType (AddInternal va) m a t = VariadicType va m a -> t
  type ResultType (AddInternal va) m a = a

  applyVFn _ f va = wrap (\ unwrap addI -> addI $ f unwrap addI (lowerVArg (Proxy :: Proxy va) va unwrap addI))

instance (VariadicArg va, VariadicFunction vf) => VariadicFunction (Func va vf) where
  type VarFnType  (Func va vf) m a t = (VariadicType va m a) -> VarFnType vf m a t
  type ResultType (Func va vf) m a   = ResultType vf m a

  applyVFn _ f va = applyVFn (Proxy :: Proxy vf)
                             (\ unwrap addI -> f unwrap addI (lowerVArg (Proxy :: Proxy va) va unwrap addI))
