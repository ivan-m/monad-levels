{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances,
             MultiParamTypeClasses, RankNTypes, TupleSections, TypeFamilies,
             TypeOperators, UndecidableInstances #-}

{- |
   Module      : Control.Monad.Levels.Definitions
   Description : Specific levls of monad transformers
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : 3-Clause BSD-style
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Control.Monad.Levels.Definitions where

import Control.Applicative    (Applicative, WrappedMonad)
import Data.Constraint        ((:-) (..), Class (..), Constraint, Dict (..),
                               trans, weaken1, weaken2, (\\))
import Data.Constraint.Forall (Forall, inst)
import Data.Proxy             (Proxy (..))

import           Control.Monad.Trans.Cont          (ContT (..))
import           Control.Monad.Trans.Except        (ExceptT (..), runExceptT)
import           Control.Monad.Trans.Identity      (IdentityT (..))
import           Control.Monad.Trans.List          (ListT (..))
import           Control.Monad.Trans.Maybe         (MaybeT (..))
import           Control.Monad.Trans.Reader        (ReaderT (..))
import qualified Control.Monad.Trans.RWS.Lazy      as LRWS
import qualified Control.Monad.Trans.RWS.Strict    as SRWS
import qualified Control.Monad.Trans.State.Lazy    as LSt
import qualified Control.Monad.Trans.State.Strict  as SSt
import qualified Control.Monad.Trans.Writer.Lazy   as LW
import qualified Control.Monad.Trans.Writer.Strict as SW
import           Data.Functor.Identity             (Identity (..))

import Control.Arrow (first)
import Data.Monoid   (Monoid, mempty)

-- -----------------------------------------------------------------------------

class (Applicative m, Monad m) => MonadTower_ m where

  type BaseMonad m :: * -> *
  type BaseMonad m = m

type MonadTower m = ( MonadTower_ m, MonadTower_ (BaseMonad m)
                    , BaseMonad (BaseMonad m) ~ BaseMonad m
                    , BaseMonad m ~ BaseMonad (BaseMonad m))

-- -----------------------------------------------------------------------------

instance MonadTower_ []
instance MonadTower_ Maybe
instance MonadTower_ IO
instance MonadTower_ (Either e)
instance MonadTower_ ((->) r)
instance (Monad m) => MonadTower_ (WrappedMonad m)

instance MonadTower_ Identity

instance (MonadTower m) => MonadTower_ (ContT r m) where
  type BaseMonad (ContT r m) = BaseMonad m

instance (MonadTower m) => MonadTower_ (ExceptT e m) where
  type BaseMonad (ExceptT e m) = BaseMonad m

instance (MonadTower m) => MonadTower_ (IdentityT m) where
  type BaseMonad (IdentityT m) = BaseMonad m

instance (MonadTower m) => MonadTower_ (ListT m) where
  type BaseMonad (ListT m) = BaseMonad m

instance (MonadTower m) => MonadTower_ (MaybeT m) where
  type BaseMonad (MaybeT m) = BaseMonad m

instance (MonadTower m) => MonadTower_ (ReaderT r m) where
  type BaseMonad (ReaderT r m) = BaseMonad m

instance (Monoid w, MonadTower m) => MonadTower_ (LRWS.RWST r w s m) where
  type BaseMonad (LRWS.RWST r w s m) = BaseMonad m

instance (Monoid w, MonadTower m) => MonadTower_ (SRWS.RWST r w s m) where
  type BaseMonad (SRWS.RWST r w s m) = BaseMonad m

instance (MonadTower m) => MonadTower_ (LSt.StateT s m) where
  type BaseMonad (LSt.StateT s m) = BaseMonad m

instance (MonadTower m) => MonadTower_ (SSt.StateT s m) where
  type BaseMonad (SSt.StateT s m) = BaseMonad m

instance (Monoid w, MonadTower m) => MonadTower_ (LW.WriterT w m) where
  type BaseMonad (LW.WriterT w m) = BaseMonad m

instance (Monoid w, MonadTower m) => MonadTower_ (SW.WriterT w m) where
  type BaseMonad (SW.WriterT w m) = BaseMonad m

-- -----------------------------------------------------------------------------

class (MonadTower m, MonadTower (LowerMonad m)
      , BaseMonad m ~ BaseMonad (LowerMonad m), BaseMonad (LowerMonad m) ~ BaseMonad m
      , CanAddInternalM m)
      => MonadLevel_ m where

  type LowerMonad m :: * -> *

  type InnerValue m a :: *
  type InnerValue m a = a

  type WithLower_ m :: (* -> *) -> * -> *
  type WithLower_ m = AddIdent

  -- | Within the continuation for 'wrap' for @m a@, we can unwrap any
  --   @m b@ if @AllowOtherValues m ~ True@; otherwise, we can only
  --   unwrap @m a@.
  type AllowOtherValues m :: Bool
  type AllowOtherValues m = True

  type DefaultAllowConstraints m :: Bool
  type DefaultAllowConstraints m = True

  wrap :: (CanUnwrap m a b) => Proxy a
          -> (Unwrapper m a (LowerMonadValue m b)) -> m b

type CanUnwrap_ m a b = CheckOtherAllowed (AllowOtherValues m) a b

type family CheckOtherAllowed (allowed::Bool) a b :: Constraint where
  CheckOtherAllowed True  a b = ()
  CheckOtherAllowed False a b = (a ~ b)

class (MonadLevel_ m, CanUnwrap_ m a b) => CanUnwrap m a b
instance (MonadLevel_ m, CanUnwrap_ m a b) => CanUnwrap m a b

class (MonadLevel_ m, CanUnwrap m a a) => CanUnwrapSelf m a
instance (MonadLevel_ m, CanUnwrap m a a) => CanUnwrapSelf m a

instance (MonadLevel_ m) => Class (MonadLevel_ m, CanUnwrap m a a) (CanUnwrapSelf m a) where
  cls = Sub Dict

getUnwrapSelfProof :: (MonadLevel m) => MonadLevel m :- CanUnwrap m a a
getUnwrapSelfProof = trans weaken2                       -- CanUnwrap
                           ( trans cls                   -- Undo CanUnwrapSelf
                                   (trans inst           -- Undo Forall
                                          (trans weaken1 -- Get Forall
                                                 weaken2 -- Remove MonadLevel_
                                          )
                                   )
                           )

type MonadLevel m = (MonadLevel_ m, (Forall (CanUnwrapSelf m), WithLowerC m))

type LowerMonadValue m a = LowerMonad m (InnerValue m a)

type Unwrapper m a t =    (forall b. (CanUnwrap m a b) => m b -> LowerMonadValue m b)
                       -> (WithLower m a)
                       -> t

type WithLower m = WithLower_ m m
type WithLowerC m = AddConstraint (WithLower_ m) m

type CanAddInternalM m = AddInternalM (WithLower_ m)
type CanAddInternal  m = AddInternal  (WithLower_ m)
type CanGetInternal  m = GetInternal  (WithLower_ m)

class AddInternalM (ai :: (* -> *) -> * -> *) where

  type AddConstraint ai (m :: * -> *) :: Constraint
  type AddConstraint ai m             = ()

  addInternalM :: (MonadLevel m, WithLower_ m ~ ai, CanUnwrap m a b)
                  => ai m a -> LowerMonad m b
                  -> LowerMonadValue m b

class (AddInternalM ai) => AddInternal ai where
  addInternal :: (MonadLevel m, WithLower_ m ~ ai, CanUnwrap m a b)
                 => ai m a -> b -> InnerValue m b

  mapInternal :: (MonadLevel m, WithLower_ m ~ ai, CanUnwrap m a b, CanUnwrap m a c)
                 => ai m a -> (b -> c) -> InnerValue m b -> InnerValue m c

class (AddInternal ai) => GetInternal ai where
  getInternal :: (MonadLevel m, WithLower_ m ~ ai, CanUnwrap m a b)
                 => ai m a -> c -> (b -> c) -> InnerValue m b -> c

newtype AddIM m a = AddIM { addIMFunc :: forall b. (CanUnwrap m a b)
                                         => LowerMonad m b -> LowerMonadValue m b }

instance AddInternalM AddIM where
  addInternalM = addIMFunc

data AddI m a = AddI { setIFunc :: forall b. (CanUnwrap m a b) => b -> InnerValue m b
                     , mapIFunc :: forall b c. (CanUnwrap m a b, CanUnwrap m a c)
                                               => (b -> c) -> InnerValue m b -> InnerValue m c
                     }

instance AddInternalM AddI where
  addInternalM ai = fmap (setIFunc ai)

addIntProof :: (MonadLevel m, AddInternalM ai) => ai m a -> MonadLevel m :- CanUnwrap m a a
addIntProof _ = getUnwrapSelfProof

instance AddInternal AddI where
  addInternal = setIFunc

  mapInternal = mapIFunc

data AddIG m a = AddIG { setIUFunc :: forall b. (CanUnwrap m a b) => b -> InnerValue m b
                       , mapIUFunc :: forall b c. (CanUnwrap m a b, CanUnwrap m a c)
                                                  => (b -> c) -> InnerValue m b -> InnerValue m c
                       , getIUFunc :: forall b c. (CanUnwrap m a b)
                                                  => c -> (b -> c) -> InnerValue m b -> c
                       }

instance AddInternalM AddIG where
  addInternalM ai = fmap (setIUFunc ai)

instance AddInternal AddIG where
  addInternal = setIUFunc

  mapInternal = mapIUFunc

instance GetInternal AddIG where
  getInternal = getIUFunc

data AddIdent (m :: * -> *) a = AddIdent

instance AddInternalM AddIdent where
  type AddConstraint AddIdent m = Forall (InnerSame m)

  addInternalM ai m = m \\ addIdentProof ai (proxyFromM m)

class (MonadLevel_ m, InnerValue m a ~ a) => InnerSame m a
instance (MonadLevel_ m, InnerValue m a ~ a) => InnerSame m a

addIdentProof :: AddIdent m a -> Proxy b -> Forall (InnerSame m) :- InnerSame m b
addIdentProof _ _ = inst

proxyFrom :: a -> Proxy a
proxyFrom _ = Proxy

proxyFromM :: m a -> Proxy a
proxyFromM _ = Proxy

proxyFromF1 :: (a -> b) -> Proxy a
proxyFromF1 _ = Proxy

proxyFromF2 :: (a -> b) -> Proxy b
proxyFromF2 _ = Proxy

instance AddInternal AddIdent where
  addInternal ai b = b \\ addIdentProof ai (proxyFrom b)

  mapInternal ai f = f \\ addIdentProof ai (proxyFromF2 f)
                       \\ addIdentProof ai (proxyFromF1 f)

instance GetInternal AddIdent where
  getInternal ai _ f lb = f lb \\ addIdentProof ai (proxyFromF1 f)

-- -----------------------------------------------------------------------------

instance (MonadTower m) => MonadLevel_ (ContT r m) where
  type LowerMonad (ContT r m) = m
  type InnerValue (ContT r m) a = r
  type WithLower_ (ContT r m) = AddIM
  type AllowOtherValues (ContT r m) = False
  type DefaultAllowConstraints (ContT r m) = False

  wrap _ f = ContT $ \ cont -> f (`runContT` cont) (AddIM (>>= cont))

instance (MonadTower m) => MonadLevel_ (ExceptT e m) where
  type LowerMonad (ExceptT e m) = m
  type InnerValue (ExceptT e m) a = Either e a
  type WithLower_ (ExceptT e m) = AddIG

  wrap _ f = ExceptT $ f runExceptT (AddIG Right fmap (either . const))

instance (MonadTower m) => MonadLevel_ (IdentityT m) where
  type LowerMonad (IdentityT m) = m

  wrap _ f = IdentityT $ f runIdentityT AddIdent

instance (MonadTower m) => MonadLevel_ (ListT m) where
  type LowerMonad (ListT m) = m
  type InnerValue (ListT m) a = [a]
  type WithLower_ (ListT m) = AddI
  type DefaultAllowConstraints (ListT m) = False

  wrap _ f = ListT $ f runListT (AddI (:[]) map)
  -- Can't define getInternal as that would require length <= 1

instance (MonadTower m) => MonadLevel_ (MaybeT m) where
  type LowerMonad (MaybeT m) = m
  type InnerValue (MaybeT m) a = Maybe a
  type WithLower_ (MaybeT m) = AddIG

  wrap _ f = MaybeT $ f runMaybeT (AddIG Just fmap maybe)

instance (MonadTower m) => MonadLevel_ (ReaderT r m) where
  type LowerMonad (ReaderT r m) = m

  wrap _ f = ReaderT $ \ r -> f (`runReaderT` r) AddIdent

map1 :: (a -> a') -> (a,b,c) -> (a',b,c)
map1 f (a,b,c) = (f a,b,c)
{-# INLINE map1 #-}

get1 :: (a,b,c) -> a
get1 (a,_,_) = a
{-# INLINE get1 #-}

instance (Monoid w, MonadTower m) => MonadLevel_ (LRWS.RWST r w s m) where
  type LowerMonad (LRWS.RWST r w s m) = m
  type InnerValue (LRWS.RWST r w s m) a = (a,s,w)
  type WithLower_ (LRWS.RWST r w s m) = AddIG

  wrap _ f = LRWS.RWST $ \ r s -> f (\m -> LRWS.runRWST m r s) (AddIG (,s,mempty) map1 (const (. get1)))

instance (Monoid w, MonadTower m) => MonadLevel_ (SRWS.RWST r w s m) where
  type LowerMonad (SRWS.RWST r w s m) = m
  type InnerValue (SRWS.RWST r w s m) a = (a,s,w)
  type WithLower_ (SRWS.RWST r w s m) = AddIG

  wrap _ f = SRWS.RWST $ \ r s -> f (\m -> SRWS.runRWST m r s) (AddIG (,s,mempty) map1 (const (. get1)))

instance (MonadTower m) => MonadLevel_ (LSt.StateT s m) where
  type LowerMonad (LSt.StateT s m) = m
  type InnerValue (LSt.StateT s m) a = (a,s)
  type WithLower_ (LSt.StateT s m) = AddIG

  wrap _ f = LSt.StateT $ \ s -> f (`LSt.runStateT` s) (AddIG (,s) first (const (. fst)))

instance (MonadTower m) => MonadLevel_ (SSt.StateT s m) where
  type LowerMonad (SSt.StateT s m) = m
  type InnerValue (SSt.StateT s m) a = (a,s)
  type WithLower_ (SSt.StateT s m) = AddIG

  wrap _ f = SSt.StateT $ \ s -> f (`SSt.runStateT` s) (AddIG (,s) first (const (. fst)))

instance (Monoid w, MonadTower m) => MonadLevel_ (LW.WriterT w m) where
  type LowerMonad (LW.WriterT w m) = m
  type InnerValue (LW.WriterT w m) a = (a,w)
  type WithLower_ (LW.WriterT w m) = AddIG

  wrap _ f = LW.WriterT $ f LW.runWriterT (AddIG (,mempty) first (const (. fst)))

instance (Monoid w, MonadTower m) => MonadLevel_ (SW.WriterT w m) where
  type LowerMonad (SW.WriterT w m) = m
  type InnerValue (SW.WriterT w m) a = (a,w)
  type WithLower_ (SW.WriterT w m) = AddIG

  wrap _ f = SW.WriterT $ f SW.runWriterT (AddIG (,mempty) first (const (. fst)))

-- -----------------------------------------------------------------------------

class (MonadTower m, m ~ BaseMonad m, BaseMonad m ~ m) => IsBaseMonad m

instance (MonadTower m, m ~ BaseMonad m, BaseMonad m ~ m) => IsBaseMonad m

type family SameMonad (m :: * -> *) (n :: * -> *) where
  SameMonad m m = True
  SameMonad m n = False

-- -----------------------------------------------------------------------------

-- | When considering whether a particular monad within a 'MonadTower'
--   stack satisfies a constraint, we need to be able to determine
--   this at the type level.
--
--   This is achieved with the 'ConstraintSatisfied' associated type:
--   it should be equated to a closed type family with the result
--   being 'True' for all monads for which the constraint is satisfied
--   and 'False' for all others.
--
--   (This is defined as a type class rather than just a type family
--   so that we can explicitly state that this needs to be defined.)
class ValidConstraint (c :: (* -> *) -> Constraint) where
  type ConstraintSatisfied c (m :: * -> *) :: Bool

instance ValidConstraint IsBaseMonad where
  type ConstraintSatisfied IsBaseMonad m = SameMonad (BaseMonad m) m
