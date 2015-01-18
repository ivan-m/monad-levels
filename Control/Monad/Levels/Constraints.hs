{-# LANGUAGE ConstraintKinds, DataKinds, DefaultSignatures, FlexibleContexts,
             FlexibleInstances, KindSignatures, MultiParamTypeClasses,
             RankNTypes, ScopedTypeVariables, TypeFamilies, TypeOperators,
             UndecidableInstances #-}

-- unsafeCoerceConstraint is used to prevent the need for a complex
-- induction proof (which I'm not sure can actually be achieved).
{-# LANGUAGE Trustworthy #-}
{- |
   Module      : Control.Monad.Levels.Constraints
   Description : A Level-based approach to constraints
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : 3-Clause BSD-style
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Control.Monad.Levels.Constraints
       ( SatisfyConstraint
       , SatisfyConstraintF
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
       , MonadicOther
       , ValueOnly
       , Const
       , VariadicArg
       , VariadicType
       , VariadicFunction
       , VarFunction
       ) where

import Control.Monad.Levels.ConstraintPassing
import Control.Monad.Levels.Definitions

import Data.Constraint
import Data.Constraint.Unsafe (unsafeCoerceConstraint)
import Data.Proxy             (Proxy (..))

-- -----------------------------------------------------------------------------

data Nat = Zero | Suc Nat

predP :: Proxy (Suc n) -> Proxy n
predP _ = Proxy

class (ValidConstraint c, MonadTower m) => SatisfyConstraint_ (n :: Nat) c m where

  type SatMonad_ n c m :: * -> *

  type SatValue_ n c m a

  type CanLowerFunc f n c m a :: Constraint

  _liftSat :: Proxy n -> Proxy c -> SatMonad_ n c m a -> m a

  _lower :: (VariadicFunction f, CanLowerFunc f n c m a)
            => Proxy n -> Proxy c -> Proxy f -> Proxy m -> Proxy a
            -> VarFunctionSat f n c m a
            -> VarFunction f m a

instance (ValidConstraint c, MonadTower m, c m) => SatisfyConstraint_ Zero c m where

  type SatMonad_ Zero c m   = m

  type SatValue_ Zero c m a = a

  type CanLowerFunc f Zero c m a = ()

  _liftSat _ _ m = m

  _lower _n c vf m _a f = f \\ validSatFunc0 c m vf

instance (ConstraintPassThrough c m True, SatisfyConstraint_ n c (LowerMonad m))
         => SatisfyConstraint_ (Suc n) c m where

  type SatMonad_ (Suc n) c m   = SatMonad_ n c (LowerMonad m)

  type SatValue_ (Suc n) c m a = SatValue_ n c (LowerMonad m) (InnerValue m a)

  type CanLowerFunc f (Suc n) c m a = ( (CanLower f m a)
                                      , (CanLowerFunc (LowerV f m) n c (LowerMonad m) (InnerValue m a)))

  _liftSat n c m = wrap (\ _unwrap addI -> addInternalM addI (_liftSat (predP n) c m))

  _lower n c vf m a f = applyVFn vf m a (\ _unwrap _addI -> _lower (predP n)
                                                                   c
                                                                   (plowerF m vf)
                                                                   (lowerP m)
                                                                   (innerP m a)
                                                                   f
                                                                   \\ validLowerFunc m vf
                                                                   \\ validSatFunc n c m vf)
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

type SatisfyConstraintF c m a f = ( SatisfyConstraint c m
                                  , VariadicFunction f
                                  , CanLowerFunc f (SatDepth c m) c m a)

liftSat :: forall c m a. (SatisfyConstraint c m) =>
           Proxy c -> SatMonad c m a -> m a
liftSat p m = _liftSat (Proxy :: Proxy (SatDepth c m)) p m

type SatFunction c f m a = VarFunctionSat f (SatDepth c m) c m a

type SatMonadValue c m a = SatMonad_ (SatDepth c m) c m (SatValue_ (SatDepth c m) c m a)

lowerSat :: forall c m a f. (SatisfyConstraintF c m a f) =>
            Proxy c -> Proxy f -> Proxy m -> Proxy a
            -> SatFunction c f m a -> VarFunction f m a
lowerSat c vf m a f = _lower n c vf m a f
  where
    n :: Proxy (SatDepth c m)
    n = Proxy

type MFunc = MkVarFn MonadicValue

lowerFunction :: forall c m a. (SatisfyConstraint c m) => Proxy c
                 -> (SatMonadValue c m a -> SatMonadValue c m a)
                 -> m a -> m a
lowerFunction c f = lowerSat c vf m a f \\ funcProof n c m a
  where
    vf :: Proxy MFunc
    vf = Proxy

    n :: Proxy (SatDepth c m)
    n = Proxy

    m :: Proxy m
    m = Proxy

    a :: Proxy a
    a = Proxy

funcProof :: (SatisfyConstraint_ n c m)
             => Proxy n -> Proxy c -> Proxy m -> Proxy a
             -> SatisfyConstraint c m :- (CanLowerFunc MFunc n c m a)
funcProof _ _ _ _ = unsafeCoerceConstraint
{-# INLINE funcProof #-}
-- Will always be @~ ()@ by construction, but an actual proof would
-- need to be by induction.

-- -----------------------------------------------------------------------------

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

class VariadicLower v where

  type LowerV v (m :: * -> *) :: *
  type LowerV v m = v

  type SatV v (n :: Nat) (c :: (* -> *) -> Constraint) (m :: * -> *) :: *
  type SatV v n c m = v

  type CanLower v (m :: * -> *) a :: Constraint
  type CanLower v m             a = ()

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
class (VariadicLower v) => VariadicArg v where

  -- | The type that the variadic guard corresponds to within the
  --   monad @(m a)@.
  type VariadicType v (m :: * -> *) a

  validSatArg0 :: (SatisfyConstraint_ Zero c m)
                  => Proxy c -> Proxy m -> Proxy v
                  -> SatisfyConstraint_ Zero c m :- SatV v Zero c m ~ v
  default validSatArg0 :: (SatisfyConstraint_ Zero c m)
                          => Proxy c -> Proxy m -> Proxy v
                          -> SatisfyConstraint_ Zero c m :- v ~ v
  validSatArg0 _ _ _ = Sub Dict

  validSatArg :: (SatisfyConstraint_ (Suc n) c m)
                 => Proxy (Suc n) -> Proxy c -> Proxy m -> Proxy v
                 -> SatisfyConstraint_ (Suc n) c m
                    :- SatV v (Suc n) c m ~ SatV (LowerV v m) n c (LowerMonad m)
  default validSatArg :: (SatisfyConstraint_ (Suc n) c m)
                         => Proxy (Suc n) -> Proxy c -> Proxy m -> Proxy v
                         -> SatisfyConstraint_ (Suc n) c m
                            :- v ~ v
  validSatArg _ _ _ _ = Sub Dict

class (VariadicArg v) => LowerableVArg v where

  validLowerArg :: (MonadLevel m) => Proxy m -> Proxy v -> MonadLevel m :- LowerableVArg (LowerV v m)
  default validLowerArg :: (MonadLevel m, LowerV v m ~ v)
                           => Proxy m -> Proxy v -> MonadLevel m :- LowerableVArg v
  validLowerArg _ _ = Sub Dict

  lowerVArg :: (MonadLevel m, CanLower v m a)
               => Proxy v -> Proxy m -> Proxy a
               -> VariadicType v m a
               -> Unwrapper m a (LowerVArg v m a)

class (VariadicArg v) => LiftableVArg v where

  validLiftArg :: (MonadLevel m) => Proxy m -> Proxy v -> MonadLevel m :- LiftableVArg (LowerV v m)
  default validLiftArg :: (MonadLevel m, LowerV v m ~ v)
                          => Proxy m -> Proxy v -> MonadLevel m :- LiftableVArg v
  validLiftArg _ _ = Sub Dict

  liftVArg :: (MonadLevel m, CanLower v m a)
              => Proxy v -> Proxy m -> Proxy a
              -> LowerVArg v m a
              -> Unwrapper m a (VariadicType v m a)

type LowerVArg v m a = VariadicType (LowerV v m) (LowerMonad m) (InnerValue m a)

-- | A constant type that does not depend upon the current monadic
--   context.  That is, @Const b@ corresponds to just @b@.  It is kept
--   as-is when lowering through the different levels.
data Const (b :: *)

instance VariadicLower (Const b)

instance VariadicArg (Const b) where
  type VariadicType (Const b) m a = b

instance LowerableVArg (Const b) where

  lowerVArg _ _ _ b _ _ = b

instance LiftableVArg (Const b) where

  liftVArg  _ _ _ b _ _ = b

-- | Corresponds to @m a@.
data MonadicValue

instance VariadicLower MonadicValue

instance VariadicArg MonadicValue where
  type VariadicType MonadicValue m a = m a

instance LowerableVArg MonadicValue where

  lowerVArg _ pm pa m unwrap _ = unwrap m \\ (proofInst pm pa)

instance LiftableVArg MonadicValue where

  liftVArg  _ _ _ m _      _ = wrap (\ _ _ -> m)

proofInst :: (MonadLevel m) => Proxy m -> Proxy a -> (MonadLevel m :- CanUnwrap m a a)
proofInst _ _ = getUnwrapSelfProof
{-# INLINE proofInst #-}

-- | Corresponds to @m b@, where the final result is @m a@.
data MonadicOther b

instance VariadicLower (MonadicOther b) where
  type LowerV (MonadicOther b) m = MonadicOther (InnerValue m b)

  type SatV (MonadicOther b) n c m = MonadicOther (SatValue_ n c m b)

  type CanLower (MonadicOther b) m a = CanUnwrap m a b

instance VariadicArg (MonadicOther b) where
  type VariadicType (MonadicOther b) m a = m b

  validSatArg0 _ _ _ = Sub Dict

  validSatArg _ _ _ _ = Sub Dict

instance LowerableVArg (MonadicOther b) where

  validLowerArg _ _ = Sub Dict

  lowerVArg _ _ _ m unwrap _ = unwrap m

instance LiftableVArg (MonadicOther b) where

  validLiftArg _ _ = Sub Dict

  liftVArg _ _ _ m _ _ = wrap (\ _ _ -> m)

-- | This corresponds to @a@ when the final result is @m a@.
data ValueOnly

instance VariadicLower ValueOnly where
  type CanLower ValueOnly m a = CanAddInternal m

instance VariadicArg ValueOnly where
  type VariadicType ValueOnly m a = a

instance LowerableVArg ValueOnly where

  lowerVArg _ _ _ a _ addI = addInternal addI a

-- | Represents the function @a -> b@.
data Func (a :: *) (b :: *)

pfa :: Proxy (Func a b) -> Proxy a
pfa _ = Proxy

pfb :: Proxy (Func a b) -> Proxy b
pfb _ = Proxy

instance (VariadicLower a, VariadicLower b) => VariadicLower (Func a b) where
  type LowerV (Func va vb) m = Func (LowerV va m) (LowerV vb m)

  type SatV (Func va vb) n c m = Func (SatV va n c m) (SatV vb n c m)

  type CanLower (Func va vb) m a = ((CanLower va m a), (CanLower vb m a))

instance (VariadicArg va, VariadicArg vb) => VariadicArg (Func va vb) where
  type VariadicType (Func va vb) m a = VariadicType va m a -> VariadicType vb m a

  validSatArg0 c m f = Sub Dict \\ validSatArg0 c m (pfa f)
                                \\ validSatArg0 c m (pfb f)

  validSatArg n c m f = Sub Dict \\ validSatArg n c m (pfa f)
                                 \\ validSatArg n c m (pfb f)

instance (LiftableVArg va, LowerableVArg vb) => LowerableVArg (Func va vb) where

  validLowerArg m f = Sub Dict \\ validLiftArg m  (pfa f)
                               \\ validLowerArg m (pfb f)

  -- lower . f . lift
  lowerVArg pf m a f unwrap addI
    =   (\ v -> lowerVArg (pfb pf) m a v unwrap addI)
      . f
      . (\ v -> liftVArg  (pfa pf) m a v unwrap addI)

instance (LowerableVArg va, LiftableVArg vb) => LiftableVArg (Func va vb) where

  validLiftArg m f = Sub Dict \\ validLowerArg m (pfa f)
                              \\ validLiftArg m  (pfb f)

  -- lift . f . lower
  liftVArg pf m a f unwrap addI
    =   (\ v -> liftVArg  (pfb pf) m a v unwrap addI)
      . f
      . (\ v -> lowerVArg (pfa pf) m a v unwrap addI)

-- | A function composed of variadic arguments that produces a value
--   of type @m a@.
class (VariadicLower f) => VariadicFunction f where

  -- | The function (that produces a value of type @t@) that this
  --   instance corresponds to.
  type VarFunction f (m :: * -> *) a

  validLowerFunc :: (MonadLevel m) => Proxy m -> Proxy f -> MonadLevel m :- VariadicFunction (LowerV f m)

  validSatFunc0 :: (SatisfyConstraint_ Zero c m)
                   => Proxy c -> Proxy m -> Proxy f
                   -> SatisfyConstraint_ Zero c m :- SatV f Zero c m ~ f

  validSatFunc :: (SatisfyConstraint_ (Suc n) c m)
                  => Proxy (Suc n) -> Proxy c -> Proxy m -> Proxy f
                  -> SatisfyConstraint_ (Suc n) c m
                     :- SatV f (Suc n) c m ~ SatV (LowerV f m) n c (LowerMonad m)

  applyVFn :: (MonadLevel m, CanLower f m a)
              => Proxy f -> Proxy m -> Proxy a
              -> Unwrapper m a (VarFunctionLower f m a)
              -> VarFunction f m a

type VarFunctionLower f (m :: * -> *) a = VarFunction (LowerV f m) (LowerMonad m) (InnerValue m a)

type VarFunctionSat f n c m a = VarFunction (SatV f n c m) (SatMonad_ n c m) (SatValue_ n c m a)

plowerF :: (MonadLevel m, VariadicFunction f) => Proxy m -> Proxy f -> Proxy (LowerV f m)
plowerF _ _ = Proxy

data MkVarFn va

pmvf :: Proxy (MkVarFn va) -> Proxy va
pmvf _ = Proxy

instance (VariadicLower va) => VariadicLower (MkVarFn va) where
  type LowerV (MkVarFn va) m = MkVarFn (LowerV va m)

  type SatV (MkVarFn va) n c m = MkVarFn (SatV va n c m)

  type CanLower (MkVarFn va) m a = CanLower va m a

instance (LowerableVArg va) => VariadicFunction (MkVarFn va) where

  type VarFunction (MkVarFn va) m a = VariadicType va m a -> m a

  validLowerFunc m pmf = Sub Dict \\ validLowerArg m (pmvf pmf)

  validSatFunc0 c m pmf = Sub Dict \\ validSatArg0 c m (pmvf pmf)

  validSatFunc n c m pmf = Sub Dict \\ validSatArg n c m (pmvf pmf)

  applyVFn pmf m a f va = wrap (\ unwrap addI ->
                                f unwrap addI (lowerVArg (pmvf pmf) m a va unwrap addI))

instance (LowerableVArg va, VariadicFunction vf) => VariadicFunction (Func va vf) where
  type VarFunction (Func va vf) m a = (VariadicType va m a) -> VarFunction vf m a

  validLowerFunc m f = Sub Dict \\ validLowerArg  m (pfa f)
                                \\ validLowerFunc m (pfb f)

  validSatFunc0 c m f = Sub Dict \\ validSatArg0  c m (pfa f)
                                 \\ validSatFunc0 c m (pfb f)

  validSatFunc n c m f = Sub Dict \\ validSatArg  n c m (pfa f)
                                  \\ validSatFunc n c m (pfb f)

  applyVFn pf m a f va = applyVFn (pfb pf) m a
                                  (\ unwrap addI ->
                                     f unwrap addI (lowerVArg (pfa pf) m a va unwrap addI))

-- -----------------------------------------------------------------------------
