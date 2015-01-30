{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances,
             MultiParamTypeClasses, TypeFamilies #-}

{- |
   Module      : Control.Monad.Levels.RWS
   Description : Monads with reader, writer and state abilities
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : 3-Clause BSD-style
   Maintainer  : Ivan.Miljenovic@gmail.com

Note that the original definitions are used for the various reader,
writer and state computations: as such, if there is (for example)
another level that satisfies 'IsReader r' above the one that satisfies
'IsRWS r w s' in the stack, then calling 'ask' will use the higher
level.

 -}
module Control.Monad.Levels.RWS
  ( HasRWS
  , IsRWS
  , module Control.Monad.Levels.Reader
  , module Control.Monad.Levels.Writer
  , module Control.Monad.Levels.State
  ) where

import Control.Monad.Levels
import Control.Monad.Levels.Constraints
import Control.Monad.Levels.Reader
import Control.Monad.Levels.State
import Control.Monad.Levels.Writer

import Data.Monoid (Monoid)

import qualified Control.Monad.Trans.RWS.Lazy   as L
import qualified Control.Monad.Trans.RWS.Strict as S

-- -----------------------------------------------------------------------------

-- | Defined as another class rather than an alias in case you need to
--   ensure the same level satisfies all three constraints (and to
--   have a specific 'ValidConstraint' instance).
class (IsReader r m, IsWriter w m, IsState s m) => IsRWS r w s m

instance (MonadTower m, Monoid w) => IsRWS r w s (L.RWST r w s m)

instance (MonadTower m, Monoid w) => IsRWS r w s (S.RWST r w s m)

instance (Monoid w) => ValidConstraint (IsRWS r w s) where
  type ConstraintSatisfied (IsRWS r w s) m = SameRWS r w s m

type family SameRWS r w s m where
  SameRWS r w s (L.RWST r w s m) = True
  SameRWS r w s (S.RWST r w s m) = True
  SameRWS r w s m                = False

type HasRWS r w s m = SatisfyConstraint (IsRWS r w s) m
