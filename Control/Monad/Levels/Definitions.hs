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
      , BaseMonad m ~ BaseMonad (LowerMonad m), BaseMonad (LowerMonad m) ~ BaseMonad m)
      => MonadLevel_ m where

  type LowerMonad m :: * -> *

  type InnerValue m a :: *
  type InnerValue m a = a

  -- | Within the continuation for 'wrap' for @m a@, we can unwrap any
  --   @m b@ where @UnwrappableValue m a b@ is satisfied.
  type CanUnwrap_ m a b :: Constraint
  type CanUnwrap_ m a b = ()

  type AllConstraintsThrough m :: Bool
  type AllConstraintsThrough m = True

  wrap :: (Forall (CanUnwrapSelf m)) => (Unwrapper m a (LowerMonadValue m a))
                                         -> m a

class (MonadLevel_ m, CanUnwrap_ m a b) => CanUnwrap m a b
instance (MonadLevel_ m, CanUnwrap_ m a b) => CanUnwrap m a b

class (MonadLevel_ m, CanUnwrap m a a) => CanUnwrapSelf m a
instance (MonadLevel_ m, CanUnwrap m a a) => CanUnwrapSelf m a

instance (MonadLevel_ m) => Class (MonadLevel_ m, CanUnwrap m a a) (CanUnwrapSelf m a) where
  cls = Sub Dict

getUnwrapSelfProof :: (MonadLevel m) => MonadLevel m :- CanUnwrap m a a
getUnwrapSelfProof = trans weaken2                -- CanUnwrap
                           ( trans cls            -- Undo CanUnwrapSelf
                                   (trans inst    -- Undo Forall
                                          weaken2 -- Get Forall
                                   )
                           )

type MonadLevel m = (MonadLevel_ m, Forall (CanUnwrapSelf m))

type LowerMonadValue m a = LowerMonad m (InnerValue m a)

type Unwrapper m a t =    (forall b. (CanUnwrap m a b) => m b -> LowerMonadValue m b)
                       -> (LowerMonad m a -> LowerMonadValue m a)
                       -> t

-- -----------------------------------------------------------------------------

instance (MonadTower m) => MonadLevel_ (ContT r m) where
  type LowerMonad (ContT r m) = m
  type InnerValue (ContT r m) a = r
  type CanUnwrap_ (ContT r m) a b = a ~ b
  type AllConstraintsThrough (ContT r m) = False

  wrap f = ContT $ \ cont -> f (`runContT` cont) (>>= cont)

instance (MonadTower m) => MonadLevel_ (ExceptT e m) where
  type LowerMonad (ExceptT e m) = m
  type InnerValue (ExceptT e m) a = Either e a

  wrap f = ExceptT $ f runExceptT (fmap Right)

instance (MonadTower m) => MonadLevel_ (IdentityT m) where
  type LowerMonad (IdentityT m) = m

  wrap f = IdentityT $ f runIdentityT id

instance (MonadTower m) => MonadLevel_ (ListT m) where
  type LowerMonad (ListT m) = m
  type InnerValue (ListT m) a = [a]
  type AllConstraintsThrough (ListT m) = False

  wrap f = ListT $ f runListT (fmap (:[]))

instance (MonadTower m) => MonadLevel_ (MaybeT m) where
  type LowerMonad (MaybeT m) = m
  type InnerValue (MaybeT m) a = Maybe a

  wrap f = MaybeT $ f runMaybeT (fmap Just)

instance (MonadTower m) => MonadLevel_ (ReaderT r m) where
  type LowerMonad (ReaderT r m) = m

  wrap f = ReaderT $ \ r -> f (`runReaderT` r) id

instance (Monoid w, MonadTower m) => MonadLevel_ (LRWS.RWST r w s m) where
  type LowerMonad (LRWS.RWST r w s m) = m
  type InnerValue (LRWS.RWST r w s m) a = (a,s,w)

  wrap f = LRWS.RWST $ \ r s -> f (\m -> LRWS.runRWST m r s) (fmap (,s,mempty))

instance (Monoid w, MonadTower m) => MonadLevel_ (SRWS.RWST r w s m) where
  type LowerMonad (SRWS.RWST r w s m) = m
  type InnerValue (SRWS.RWST r w s m) a = (a,s,w)

  wrap f = SRWS.RWST $ \ r s -> f (\m -> SRWS.runRWST m r s) (fmap (,s,mempty))

instance (MonadTower m) => MonadLevel_ (LSt.StateT s m) where
  type LowerMonad (LSt.StateT s m) = m
  type InnerValue (LSt.StateT s m) a = (a,s)

  wrap f = LSt.StateT $ \ s -> f (`LSt.runStateT` s) (fmap (,s))

instance (MonadTower m) => MonadLevel_ (SSt.StateT s m) where
  type LowerMonad (SSt.StateT s m) = m
  type InnerValue (SSt.StateT s m) a = (a,s)

  wrap f = SSt.StateT $ \ s -> f (`SSt.runStateT` s) (fmap (,s))

instance (Monoid w, MonadTower m) => MonadLevel_ (LW.WriterT w m) where
  type LowerMonad (LW.WriterT w m) = m
  type InnerValue (LW.WriterT w m) a = (a,w)

  wrap f = LW.WriterT $ f LW.runWriterT (fmap (,mempty))

instance (Monoid w, MonadTower m) => MonadLevel_ (SW.WriterT w m) where
  type LowerMonad (SW.WriterT w m) = m
  type InnerValue (SW.WriterT w m) a = (a,w)

  wrap f = SW.WriterT $ f SW.runWriterT (fmap (,mempty))

-- -----------------------------------------------------------------------------

class (MonadTower m, m ~ BaseMonad m, BaseMonad m ~ m) => IsBaseMonad m where
  idBase :: m a -> m a
  idBase = id

instance (MonadTower m, m ~ BaseMonad m, BaseMonad m ~ m) => IsBaseMonad m
