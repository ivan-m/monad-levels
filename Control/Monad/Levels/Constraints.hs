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
       , SatMonadValue
       , liftSat
       , lowerSat
       , lowerFunction
         -- * Re-exported for convenience
       , Proxy(..)
         -- * Variadic functions
       , MkVarFn
       , Func
       , MonadicValue
       , Const
       , VariadicArg
       , VariadicType
       , VariadicFunction
       , VarFunction
       ) where

import Control.Monad.Levels.ConstraintPassing
import Control.Monad.Levels.Definitions

import Data.Proxy (Proxy (..))
import GHC.Exts   (Constraint)

-- -----------------------------------------------------------------------------

data Nat = Zero | Suc Nat

class (MonadTower m) => SatisfyConstraint_ (n :: Nat) (c :: (* -> *) -> Constraint) m where

  type SatMonad_ n c m :: * -> *

  type SatValue_ n c m a

  _liftSat :: Proxy n -> Proxy c -> SatMonad_ n c m a -> m a

  _lower :: (VariadicFunction f) => Proxy n -> Proxy c -> Proxy f -> Proxy m -> Proxy a
                                    -> VarFunction f (SatMonad_ n c m) (SatValue_ n c m a)
                                    -> VarFunction f m a

instance (MonadTower m, c m) => SatisfyConstraint_ Zero c m where

  type SatMonad_ Zero c m   = m

  type SatValue_ Zero c m a = a

  _liftSat _ _ m = m

  _lower _n _c _vf _m _a f = f

instance (ConstraintCanPassThrough c m, SatisfyConstraint_ n c (LowerMonad m))
         => SatisfyConstraint_ (Suc n) c m where

  type SatMonad_ (Suc n) c m   = SatMonad_ n c (LowerMonad m)

  type SatValue_ (Suc n) c m a = SatValue_ n c (LowerMonad m) (InnerValue m a)

  _liftSat _ c m = wrap (\ _unwrap addI -> addI (_liftSat (Proxy :: Proxy n) c m))

  _lower _ c vf m a f = applyVFn vf m a (\ _unwrap _addI -> _lower (Proxy :: Proxy n)
                                                                   c
                                                                   vf
                                                                   (lowerP m)
                                                                   (innerP m a)
                                                                   f)

lowerP :: (MonadLevel m) => Proxy m -> Proxy (LowerMonad m)
lowerP _ = Proxy
{-# INLINE lowerP #-}

innerP :: (MonadLevel m) => Proxy m -> Proxy a -> Proxy (InnerValue m a)
innerP _ _ = Proxy
{-# INLINE innerP #-}

type SatisfyConstraint c m = ( SatisfyConstraint_ (SatDepth c m) c m
                             , c (SatMonad c m)
                             -- Best current way of stating that the
                             -- satisfying monad is a lower level of
                             -- the specified one.
                             , BaseMonad (SatMonad c m) ~ BaseMonad m)

liftSat :: forall c m a. (SatisfyConstraint c m) =>
           Proxy c -> SatMonad c m a -> m a
liftSat p m = _liftSat (Proxy :: Proxy (SatDepth c m)) p m

type SatAtLevel n c f m a = VarFunction f (SatMonad_ n c m) (SatValue_ n c m a)

type SatFunction c f m a = SatAtLevel (SatDepth c m) c f m a

type SatMonadValue c m a = SatMonad_ (SatDepth c m) c m (SatValue_ (SatDepth c m) c m a)

lowerSat :: forall c f m a. (SatisfyConstraint c m, VariadicFunction f) =>
            Proxy c -> Proxy f -> Proxy m -> Proxy a
            -> SatFunction c f m a -> VarFunction f m a
lowerSat c vf m a f = _lower (Proxy :: Proxy (SatDepth c m)) c vf m a f

lowerFunction :: forall c m a. (SatisfyConstraint c m) => Proxy c
                 -> (SatMonadValue c m a -> SatMonadValue c m a)
                 -> m a -> m a
lowerFunction c f = lowerSat c (Proxy :: Proxy (MkVarFn MonadicValue)) (Proxy :: Proxy m) (Proxy :: Proxy a) f

-- -----------------------------------------------------------------------------

type family ConstraintSatisfied (c :: (* -> *) -> Constraint) (m :: * -> *) :: Bool

type TrySatisfy (c :: (* -> *) -> Constraint) (m :: (* -> *)) = TrySatisfy' c (BaseMonad m) m

type family TrySatisfy' (c :: (* -> *) -> Constraint) (b :: (* -> *)) (m :: (* -> *)) :: [Bool] where
  TrySatisfy' c b b = ConstraintSatisfied c b ': '[]
  TrySatisfy' c b m = ConstraintSatisfied c m ': TrySatisfy' c b (LowerMonad m)

type family FindTrue (bms :: [Bool]) :: Nat where
  FindTrue (True  ': t) = Zero
  FindTrue (False ': t) = Suc (FindTrue t)

type SatDepth (c :: (* -> *) -> Constraint) (m :: * -> *) = FindTrue (TrySatisfy c m)

-- | The Monad in the tower that satisfies the provided constraint.
type SatMonad (c :: (* -> *) -> Constraint) (m :: * -> *) = SatMonad_ (SatDepth c m) c m

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

  liftVArg :: (MonadLevel m) => Proxy v
                             -> VariadicType v (LowerMonad m) (InnerValue m a)
                             -> Unwrapper m a (VariadicType v m a)

-- | A constant type that does not depend upon the current monadic
--   context.  That is, @Const b@ corresponds to just @b@.
data Const (b :: *)

instance VariadicArg (Const b) where
  type VariadicType (Const b) m a = b

  lowerVArg _ b _ _ = b

  liftVArg  _ b _ _ = b

-- | Corresponds to @m a@.
data MonadicValue

instance VariadicArg MonadicValue where
  type VariadicType MonadicValue m a = m a

  lowerVArg _ m unwrap _ = unwrap m

  liftVArg  _ m _      _ = wrap (\ _ _ -> m)

-- Can't have a LiftVA instance for MonadicValue as we can't lift it
-- (as we don't know what the outer monad would be, if there even is
-- one).

-- | Represents the function @a -> b@.
data Func (a :: *) (b :: *)

instance (VariadicArg va, VariadicArg vb) => VariadicArg (Func va vb) where
  type VariadicType (Func va vb) m a = VariadicType va m a -> VariadicType vb m a

  -- lower . f . lift
  lowerVArg _ f unwrap addI
    =   (\ v -> lowerVArg (Proxy :: Proxy vb) v unwrap addI)
      . f
      . (\ v -> liftVArg  (Proxy :: Proxy va) v unwrap addI)

  -- lift . f . lower
  liftVArg _ f unwrap addI
    =   (\ v -> liftVArg  (Proxy :: Proxy vb) v unwrap addI)
      . f
      . (\ v -> lowerVArg (Proxy :: Proxy va) v unwrap addI)

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

  applyVFn _ _ _ f va = wrap (\ unwrap addI ->
                                f unwrap addI (lowerVArg (Proxy :: Proxy va) va unwrap addI))

instance (VariadicArg va, VariadicFunction vf) => VariadicFunction (Func va vf) where
  type VarFunction  (Func va vf) m a = (VariadicType va m a) -> VarFunction vf m a

  applyVFn _ m a f va = applyVFn (Proxy :: Proxy vf) m a
                                 (\ unwrap addI ->
                                    f unwrap addI (lowerVArg (Proxy :: Proxy va) va unwrap addI))
