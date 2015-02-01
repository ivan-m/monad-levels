{-# LANGUAGE ConstraintKinds, DataKinds, DefaultSignatures, FlexibleContexts,
             FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables,
             TupleSections, TypeFamilies, TypeOperators, UndecidableInstances
             #-}

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
       ( -- * Constraints in the monad stack
         liftSat
       , lowerSat
       , lowerSat'
       , lowerFunction
       , SatisfyConstraint
       , SatisfyConstraintF
       , SatMonad
       , SatMonadValue
       , CanLowerFunc
       , SatFunction
       , ValidConstraint(..)
       , ConstraintPassThrough
         -- ** Internal types and classes
       , SatisfyConstraint_(SatMonad_, SatValue_, CanLowerFunc_)
       , SatDepth
       , proofInst
         -- * Variadic functions
       , VariadicFunction
       , VarFunction
       , VariadicLower
       , LowerV
       , SatV
       , CanLower
       , VarFunctionSat
       , MkVarFn
       , MkVarFnFrom
       , Func
         -- ** Variadic arguments
       , VariadicArg(VariadicType)
       , LowerableVArg
       , LiftableVArg
       , WrappableVArg
       , ValueOnly
       , Const
       , MonadicValue
       , MonadicOther
       , MonadicTuple
         -- * Re-exported for convenience
       , Proxy(..)
       ) where

import Control.Monad.Levels.ConstraintPassing
import Control.Monad.Levels.Definitions

import Data.Constraint        ((:-) (..), Constraint, Dict (..), (\\))
import Data.Constraint.Unsafe (unsafeCoerceConstraint)
import Data.Monoid            (Monoid (mempty))
import Data.Proxy             (Proxy (..), asProxyTypeOf)

-- -----------------------------------------------------------------------------

data Nat = Zero | Suc Nat

predP :: Proxy (Suc n) -> Proxy n
predP _ = Proxy

-- | Inductively find the \"floor\" in the 'MonadTower' where the
--   specified constraint is satisfied.
--
--   This class is only exported for documentation purposes: no other
--   instances are possible, and most of the internals are not safe to
--   use outside of this module.
--
--   You should use 'SatisfyConstraint' instead of this in your
--   constraints.
class (ValidConstraint c, MonadTower m) => SatisfyConstraint_ (n :: Nat) c m where

  -- | The monad in the stack that satisfies the constraint.
  type SatMonad_ n c m :: * -> *

  -- | The value in the stack within the monad that satisfies the
  --   constraint.
  type SatValue_ n c m a

  -- | The extra constraints needed to be able to lower the provided
  --   'VariadicFunction' @f@ to the satisfying monad.
  type CanLowerFunc_ f n c m a :: Constraint

  _liftSat :: Proxy n -> Proxy c -> Proxy m -> Proxy a -> SatMonad_ n c m a -> m a

  _lower :: (VariadicFunction f, CanLowerFunc_ f n c m a)
            => Proxy n -> Proxy c -> Proxy f -> Proxy m -> Proxy a
            -> VarFunctionSat f n c m a
            -> VarFunction f m a

-- | The satisfying monad for the specified constraint.
instance (ValidConstraint c, MonadTower m, c m) => SatisfyConstraint_ Zero c m where

  type SatMonad_ Zero c m   = m

  type SatValue_ Zero c m a = a

  type CanLowerFunc_ f Zero c m a = ()

  _liftSat _ _ _ _ m = m

  _lower _n c vf m _a f = f \\ validSatFunc0 c m vf

-- | Inductive step for finding the satisfying monad.  Note the usage
--   of 'ConstraintPassThrough' to ensure that only (constraint,monad
--   level) pairings that are valid are considered.
instance (ConstraintPassThrough c m True, SatisfyConstraint_ n c (LowerMonad m))
         => SatisfyConstraint_ (Suc n) c m where

  type SatMonad_ (Suc n) c m   = SatMonad_ n c (LowerMonad m)

  type SatValue_ (Suc n) c m a = SatValue_ n c (LowerMonad m) (InnerValue m a)

  type CanLowerFunc_ f (Suc n) c m a = ( (CanLower f m a)
                                       , (CanLowerFunc_ (LowerV f m) n c (LowerMonad m) (InnerValue m a)))

  _liftSat n c m a sm = wrap a (\ _unwrap addI -> addInternalM addI (_liftSat (predP n) c (lowerP m) a sm))
                        \\ proofInst m a

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

-- | For a specified constraint @c@ and 'MonadTower' @m@,
--   @SatisfyConstraint c m@ specifies that it is possible to reach a
--   monad in the tower that specifies the constraint.
type SatisfyConstraint c m = ( SatisfyConstraint_ (SatDepth c m) c m
                             , c (SatMonad c m)
                             -- Best current way of stating that the
                             -- satisfying monad is a lower level of
                             -- the specified one.
                             , BaseMonad (SatMonad c m) ~ BaseMonad m)

-- | An extension of 'SatisfyConstraint' that also ensures that any
--   additional constraints needed to satisfy a 'VariadicFunction' @f@
--   to achieve an end result based upon the type @m a@ are met.
type SatisfyConstraintF c m a f = ( SatisfyConstraint c m
                                  , VariadicFunction f
                                  , CanLowerFunc f c m a)

-- | Any additional constraints that may be needed for a specified
--   'VariadicFunction' to be valid as it is lowered to the satisfying
--   monad.
--
--   This typically matters only if 'ValueOnly' or 'MonadicOther' are
--   used.
type CanLowerFunc f c m a = CanLowerFunc_ f (SatDepth c m) c m a

-- | Lift a value of the satisfying monad to the top of the tower.
liftSat :: forall c m a. (SatisfyConstraint c m) =>
           Proxy c -> SatMonad c m a -> m a
liftSat p = _liftSat (Proxy :: Proxy (SatDepth c m)) p (Proxy :: Proxy m) (Proxy :: Proxy a)

-- | The type of the 'VariadicFunction' @f@ when the provided
--   constraint is satisfied.
type SatFunction c f m a = VarFunctionSat f (SatDepth c m) c m a

-- | Converts @m a@ into what the value in the monadic stack is where
--   the monad satisfies the provided constraint.
type SatMonadValue c m a = SatMonad_ (SatDepth c m) c m (SatValue_ (SatDepth c m) c m a)

-- | Lower a function from the top of the monad tower down to the
--   satisfying monad in which it can be applied.
lowerSat :: forall c m a f. (SatisfyConstraintF c m a f) =>
            Proxy c -> Proxy f -> Proxy m -> Proxy a
            -> SatFunction c f m a -> VarFunction f m a
lowerSat c vf m a f = _lower n c vf m a f
  where
    n :: Proxy (SatDepth c m)
    n = Proxy

type MFunc = MkVarFn MonadicValue

-- | A variant of 'lowerSat' for when @CanLower f m a ~ ()@.
lowerSat' :: forall c m a f. (SatisfyConstraint c m, VariadicFunction f)
             => Proxy c -> Proxy f -> Proxy m -> Proxy a
             -> (() :- CanLower f m a)
             -> SatFunction c f m a -> VarFunction f m a
lowerSat' c vf m a prf f = _lower n c vf m a f \\ simpleFuncProof vf c m a prf
  where
    n :: Proxy (SatDepth c m)
    n = Proxy

-- | A specialised instance of 'lowerSat' where a simple function of
--   type @m a -> m a@ is lowered to the satisfying monad.
lowerFunction :: forall c m a. (SatisfyConstraint c m) => Proxy c
                 -> (SatMonadValue c m a -> SatMonadValue c m a)
                 -> m a -> m a
lowerFunction c f = lowerSat' c vf m a (Sub Dict) f
  where
    vf :: Proxy MFunc
    vf = Proxy

    m :: Proxy m
    m = Proxy

    a :: Proxy a
    a = Proxy

simpleFuncProof :: (SatisfyConstraint c m, VariadicFunction f)
                   => Proxy f -> Proxy c -> Proxy m -> Proxy a
                   -> (() :- CanLower f m a) -> (() :- CanLowerFunc f c m a)
simpleFuncProof _ _ _ _ (Sub Dict) = unsafeCoerceConstraint
{-# INLINE simpleFuncProof #-}
-- Will always be @~ ()@ by construction, but an actual proof would
-- need to be by induction.

-- -----------------------------------------------------------------------------

-- Converts the monadic stack into a list of sub-stacks, and tests if
-- each sub-stack satisfies the constraint.
type TrySatisfy (c :: (* -> *) -> Constraint) (m :: (* -> *)) = TrySatisfy' c (BaseMonad m) m

type family TrySatisfy' (c :: (* -> *) -> Constraint) (b :: (* -> *)) (m :: (* -> *)) :: [Bool] where
  TrySatisfy' c b b = ConstraintSatisfied c b ': '[]
  TrySatisfy' c b m = ConstraintSatisfied c m ': TrySatisfy' c b (LowerMonad m)

type family FindTrue (bms :: [Bool]) :: Nat where
  FindTrue (True  ': t) = Zero
  FindTrue (False ': t) = Suc (FindTrue t)

-- | Calculate how many levels down is the satisfying monad.
type SatDepth (c :: (* -> *) -> Constraint) (m :: * -> *) = FindTrue (TrySatisfy c m)

-- | The Monad in the tower that satisfies the provided constraint.
type SatMonad (c :: (* -> *) -> Constraint) (m :: * -> *) = SatMonad_ (SatDepth c m) c m

-- -----------------------------------------------------------------------------

-- | Base class for dealing with variadic functions\/arguments.
class VariadicLower v where

  -- | The type when lowered to the 'LowerMonad'.  In most cases this
  --   will be the same value.
  type LowerV v (m :: * -> *) :: *
  type LowerV v m = v

  -- | The type when applied to the satisfying monad.
  type SatV v (n :: Nat) (c :: (* -> *) -> Constraint) (m :: * -> *) :: *
  type SatV v n c m = v

  -- | Any additional constraints needed when lowering @v@.
  type CanLower v (m :: * -> *) a :: Constraint
  type CanLower v m             a = ()

-- | Class representing arguments\/parameters for lower-able variadic
--   functions.
--
--   When considering a function with an end result based upon @m a@,
--   the following argument types are available:
--
--   [@'ValueOnly'@] corresponds to @a@.
--
--   [@'Const' b@] corresponds to some other type @b@.
--
--   [@'MonadicValue'@] corresponds to @m a@.
--
--   [@'MonadicOther' b@] corresponds to @m b@.
--
--   [@'MonadicTuple' b@] corresponds to @m (a,b)@.
--
--   [@'Func' v1 v2@] corresponds to @v1 -> v2@.
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

-- | Variadic arguments that can be lowered.  All 'VariadicArg' values
--   are instances of this class.
--
--   This actually defines how a variadic argument is lowered down to
--   the 'LowerMonad'.
class (VariadicArg v) => LowerableVArg v where

  validLowerArg :: (MonadLevel m) => Proxy m -> Proxy v -> MonadLevel m :- LowerableVArg (LowerV v m)
  default validLowerArg :: (MonadLevel m, LowerV v m ~ v)
                           => Proxy m -> Proxy v -> MonadLevel m :- LowerableVArg v
  validLowerArg _ _ = Sub Dict

  lowerVArg :: (MonadLevel m, CanLower v m a)
               => Proxy v -> Proxy m -> Proxy a
               -> VariadicType v m a
               -> Unwrapper m a (LowerVArg v m a)

-- | In contrast to 'LowerableVArg', this class is for 'VariadicArg'
--   values that can be /lifted/ from the 'LowerMonad'.
--
--   This is important for @'Func' v1 v2@ arguments, as to lower a
--   function we need to /lift/ @v1@ before applying the function, and
--   then subsequently lower the result.
--
--   All instances of 'VariadicArg' are instances of this with the
--   exception of 'ValueOnly' (as it's not always possible to convert
--   an arbitrary @'InnerValue' m a@ back into an @a@).
class (VariadicArg v) => LiftableVArg v where

  validLiftArg :: (MonadLevel m) => Proxy m -> Proxy v -> MonadLevel m :- LiftableVArg (LowerV v m)
  default validLiftArg :: (MonadLevel m, LowerV v m ~ v)
                          => Proxy m -> Proxy v -> MonadLevel m :- LiftableVArg v
  validLiftArg _ _ = Sub Dict

  liftVArg :: (MonadLevel m, CanLower v m a)
              => Proxy v -> Proxy m -> Proxy a
              -> LowerVArg v m a
              -> Unwrapper m a (VariadicType v m a)

-- | Variadic arguments that can be lifted via a call to 'wrap'.  Only
--   those that have a 'VariadicType' that is a monadic value can thus
--   be instances of this class.
class (LiftableVArg v) => WrappableVArg v where

  validWrapArg :: (MonadLevel m) => Proxy m -> Proxy v -> MonadLevel m :- WrappableVArg (LowerV v m)
  default validWrapArg :: (MonadLevel m, LowerV v m ~ v)
                          => Proxy m -> Proxy v -> MonadLevel m :- WrappableVArg v
  validWrapArg _ _ = Sub Dict

  wrapVArg :: (MonadLevel m, CanLower v m a)
              => Proxy v -> Proxy m -> Proxy a
              -> Unwrapper m a (LowerVArg v m a) -> VariadicType v m a

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

  liftVArg _ m a mv _      _ = wrap a (\ _ _ -> mv) \\ proofInst m a

instance WrappableVArg MonadicValue where

  wrapVArg _ m a f = wrap a f \\ proofInst m a

-- | Whilst 'MonadLevel' requires @CanUnwrap m a a@ for all @a@, the
--   type system can't always determine this.  This is a helper
--   function to do so.
proofInst :: (MonadLevel m) => Proxy m -> Proxy a -> (MonadLevel m :- CanUnwrap m a a)
proofInst _ _ = getUnwrapSelfProof
{-# INLINE proofInst #-}

-- | Corresponds to @m b@, where the final result is based upon @m a@.
--   This requires the extra constraint of @'CanUnwrap' m a b@.
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

  liftVArg _ _ a m _ _ = wrap a (\ _ _ -> m)

instance WrappableVArg (MonadicOther b) where

  validWrapArg _ _ = Sub Dict

  wrapVArg _ _ a f = wrap a f

-- | Corresponds to @m (a,b)@.  This requires the extra constraints of
--   @'CanAddInternal' m@ and @'AllowOtherValues' m ~ True@ (This is
--   used instead of 'CanUnwrap' as a simplification).
data MonadicTuple b

instance VariadicLower (MonadicTuple b) where
  type CanLower (MonadicTuple b) m a = (CanGetInternal m, AllowOtherValues m ~ True)

instance VariadicArg (MonadicTuple b) where
  type VariadicType (MonadicTuple b) m a = m (a,b)

instance (Monoid b) => LowerableVArg (MonadicTuple b) where

  lowerVArg v _ a lm unwrap addI = fmap shiftI (unwrap lm)
    where
      b = tupleProxy v

      ab = proxyPair a b

      shiftI iv = let bv = getInternal addI mempty (snd . (`asProxyTypeOf` ab)) iv
                  in (mapInternal addI (fst . (`asProxyTypeOf` ab)) iv, bv)

tupleProxy :: Proxy (MonadicTuple b) -> Proxy b
tupleProxy _ = Proxy
{-# INLINE tupleProxy #-}

proxyPair :: Proxy a -> Proxy b -> Proxy (a,b)
proxyPair _ _ = Proxy
{-# INLINE proxyPair #-}

instance LiftableVArg (MonadicTuple b) where

  liftVArg _ _ a mab _ addI = wrap a ( \ _ _ -> fmap shiftI mab)
    where
      shiftI (iva,b) = mapInternal addI ((,b) . (`asProxyTypeOf`a)) iva

instance WrappableVArg (MonadicTuple b) where

  wrapVArg _ _ a f = wrap a ( \ unwrap addI -> fmap (shiftI addI) (f unwrap addI))
    where
      shiftI ai (iva, b) = mapInternal ai ((,b) . (`asProxyTypeOf`a)) iva

-- | This corresponds to @a@ when the final result is based upon @m
--   a@.  This requires the extra constraint of @'CanAddInternal' m@.
data ValueOnly

instance VariadicLower ValueOnly where
  type CanLower ValueOnly m a = CanAddInternal m

instance VariadicArg ValueOnly where
  type VariadicType ValueOnly m a = a

instance LowerableVArg ValueOnly where

  lowerVArg _ _ _ a _ addI = addInternal addI a \\ addIntProof addI

-- | Represents the function @v1 -> v2@.
data Func (v1 :: *) (v2 :: *)

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
--   based upon the type @m a@.
class (VariadicLower f) => VariadicFunction f where

  -- | The function (that produces a value based upon the type @m a@)
  --   that this instance corresponds to.
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

-- | The function represented by the 'VariadicFunction' when lowered
--   to the satisfying monad.
type VarFunctionSat f n c m a = VarFunction (SatV f n c m) (SatMonad_ n c m) (SatValue_ n c m a)

plowerF :: (MonadLevel m, VariadicFunction f) => Proxy m -> Proxy f -> Proxy (LowerV f m)
plowerF _ _ = Proxy

-- | The fundamental way of creating a 'VariadicFunction'.  @MkVarFn
--   v@ corresponds to a function of type @'VariadicType' v m a -> m
--   a@ for some specified @m a@.
--
--   If more than one argument is needed for a function, they can be
--   prepended on using 'Func'.
type MkVarFn v = Func v (MkVarFnFrom MonadicValue)

-- | The result of a 'VariadicFunction'. This can't be used on its
--   own, and needs to have at least one 'Func' attached to it.
data MkVarFnFrom va

pmvff :: Proxy (MkVarFnFrom va) -> Proxy va
pmvff _ = Proxy

instance (VariadicLower va) => VariadicLower (MkVarFnFrom va) where
  type LowerV (MkVarFnFrom va) m = MkVarFnFrom (LowerV va m)

  type SatV (MkVarFnFrom va) n c m = MkVarFnFrom (SatV va n c m)

  type CanLower (MkVarFnFrom va) m a = CanLower va m a

instance (WrappableVArg va) => VariadicFunction (MkVarFnFrom va) where

  type VarFunction (MkVarFnFrom va) m a = VariadicType va m a

  validLowerFunc m pmf = Sub Dict \\ validWrapArg m (pmvff pmf)

  validSatFunc0 c m pmf = Sub Dict \\ validSatArg0 c m (pmvff pmf)

  validSatFunc n c m pmf = Sub Dict \\ validSatArg n c m (pmvff pmf)

  applyVFn pmf m a f = wrapVArg (pmvff pmf) m a f

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
