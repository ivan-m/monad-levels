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

import Control.Applicative
import Data.Constraint
import Data.Constraint.Forall

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
import           Data.Functor.Identity

import Data.Monoid (Monoid, mempty)

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

  wrap :: (Unwrapper m a (LowerMonadValue m a)) -> m a

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

class AddInternalM (ai :: (* -> *) -> * -> *) where

  type AddConstraint ai (m :: * -> *) :: Constraint
  type AddConstraint ai m             = ()

  addInternalM :: (MonadLevel m, AddConstraint ai m)
                  => ai m a -> LowerMonad m a
                  -> LowerMonadValue m a

class (AddInternalM ai) => AddInternal ai where
  addInternal :: (MonadLevel m, AddConstraint ai m)
                 => ai m a -> a -> InnerValue m a

newtype AddIM m a = AddIM { addIMFunc :: LowerMonad m a -> LowerMonadValue m a }

instance AddInternalM AddIM where
  addInternalM = addIMFunc

newtype AddI m a = AddI { addIFunc :: a -> InnerValue m a }

instance AddInternalM AddI where
  addInternalM = fmap . addIFunc

instance AddInternal AddI where
  addInternal = addIFunc

data AddIdent (m :: * -> *) a = AddIdent

instance AddInternalM AddIdent where
  type AddConstraint AddIdent m = Forall (InnerSame m)

  addInternalM ai = id \\ addIdentProof ai

class (MonadLevel_ m, InnerValue m a ~ a) => InnerSame m a
instance (MonadLevel_ m, InnerValue m a ~ a) => InnerSame m a

addIdentProof :: AddIdent m a -> Forall (InnerSame m) :- InnerSame m a
addIdentProof _ = inst

instance AddInternal AddIdent where
  addInternal ai = id \\ addIdentProof ai

-- -----------------------------------------------------------------------------

instance (MonadTower m) => MonadLevel_ (ContT r m) where
  type LowerMonad (ContT r m) = m
  type InnerValue (ContT r m) a = r
  type WithLower_ (ContT r m) = AddIM
  type AllowOtherValues (ContT r m) = False
  type DefaultAllowConstraints (ContT r m) = False

  wrap f = ContT $ \ cont -> f (`runContT` cont) (AddIM (>>= cont))

instance (MonadTower m) => MonadLevel_ (ExceptT e m) where
  type LowerMonad (ExceptT e m) = m
  type InnerValue (ExceptT e m) a = Either e a
  type WithLower_ (ExceptT e m) = AddI

  wrap f = ExceptT $ f runExceptT (AddI Right)

instance (MonadTower m) => MonadLevel_ (IdentityT m) where
  type LowerMonad (IdentityT m) = m

  wrap f = IdentityT $ f runIdentityT AddIdent

instance (MonadTower m) => MonadLevel_ (ListT m) where
  type LowerMonad (ListT m) = m
  type InnerValue (ListT m) a = [a]
  type WithLower_ (ListT m) = AddI
  type DefaultAllowConstraints (ListT m) = False

  wrap f = ListT $ f runListT (AddI (:[]))

instance (MonadTower m) => MonadLevel_ (MaybeT m) where
  type LowerMonad (MaybeT m) = m
  type InnerValue (MaybeT m) a = Maybe a
  type WithLower_ (MaybeT m) = AddI

  wrap f = MaybeT $ f runMaybeT (AddI Just)

instance (MonadTower m) => MonadLevel_ (ReaderT r m) where
  type LowerMonad (ReaderT r m) = m

  wrap f = ReaderT $ \ r -> f (`runReaderT` r) AddIdent

instance (Monoid w, MonadTower m) => MonadLevel_ (LRWS.RWST r w s m) where
  type LowerMonad (LRWS.RWST r w s m) = m
  type InnerValue (LRWS.RWST r w s m) a = (a,s,w)
  type WithLower_ (LRWS.RWST r w s m) = AddI

  wrap f = LRWS.RWST $ \ r s -> f (\m -> LRWS.runRWST m r s) (AddI (,s,mempty))

instance (Monoid w, MonadTower m) => MonadLevel_ (SRWS.RWST r w s m) where
  type LowerMonad (SRWS.RWST r w s m) = m
  type InnerValue (SRWS.RWST r w s m) a = (a,s,w)
  type WithLower_ (SRWS.RWST r w s m) = AddI

  wrap f = SRWS.RWST $ \ r s -> f (\m -> SRWS.runRWST m r s) (AddI (,s,mempty))

instance (MonadTower m) => MonadLevel_ (LSt.StateT s m) where
  type LowerMonad (LSt.StateT s m) = m
  type InnerValue (LSt.StateT s m) a = (a,s)
  type WithLower_ (LSt.StateT s m) = AddI

  wrap f = LSt.StateT $ \ s -> f (`LSt.runStateT` s) (AddI (,s))

instance (MonadTower m) => MonadLevel_ (SSt.StateT s m) where
  type LowerMonad (SSt.StateT s m) = m
  type InnerValue (SSt.StateT s m) a = (a,s)
  type WithLower_ (SSt.StateT s m) = AddI

  wrap f = SSt.StateT $ \ s -> f (`SSt.runStateT` s) (AddI (,s))

instance (Monoid w, MonadTower m) => MonadLevel_ (LW.WriterT w m) where
  type LowerMonad (LW.WriterT w m) = m
  type InnerValue (LW.WriterT w m) a = (a,w)
  type WithLower_ (LW.WriterT w m) = AddI

  wrap f = LW.WriterT $ f LW.runWriterT (AddI (,mempty))

instance (Monoid w, MonadTower m) => MonadLevel_ (SW.WriterT w m) where
  type LowerMonad (SW.WriterT w m) = m
  type InnerValue (SW.WriterT w m) a = (a,w)
  type WithLower_ (SW.WriterT w m) = AddI

  wrap f = SW.WriterT $ f SW.runWriterT (AddI (,mempty))

-- -----------------------------------------------------------------------------

class (MonadTower m, m ~ BaseMonad m, BaseMonad m ~ m) => IsBaseMonad m where
  idBase :: m a -> m a
  idBase = id

instance (MonadTower m, m ~ BaseMonad m, BaseMonad m ~ m) => IsBaseMonad m
