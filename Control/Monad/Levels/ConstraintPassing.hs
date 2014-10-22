{-# LANGUAGE DataKinds, FlexibleInstances, KindSignatures,
             MultiParamTypeClasses, OverlappingInstances, TypeFamilies #-}
{- |
   Module      : Control.Monad.Levels.ConstraintPassing
   Description : Whether a transformer allows a constraint to pass through
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : 3-Clause BSD-style
   Maintainer  : Ivan.Miljenovic@gmail.com

This module is defined separately as it's the only one that uses the
@OverlappingInstances@ extension.

 -}
module Control.Monad.Levels.ConstraintPassing where

import Control.Monad.Levels.Definitions

import GHC.Exts (Constraint)

-- -----------------------------------------------------------------------------

class (MonadLevel m) => ConstraintCanPassThrough (c :: (* -> *) -> Constraint) m

instance (MonadLevel m, AllConstraintsThrough m ~ True) => ConstraintCanPassThrough c m

instance (MonadLevel m) => ConstraintCanPassThrough IsBaseMonad m