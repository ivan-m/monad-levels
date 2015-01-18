{-# LANGUAGE ConstraintKinds, DataKinds, FlexibleContexts, FlexibleInstances,
             KindSignatures, MultiParamTypeClasses, OverlappingInstances,
             TypeFamilies, UndecidableInstances #-}
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

-- -----------------------------------------------------------------------------

class (ValidConstraint c, MonadLevel m) => ConstraintPassThrough c m (b :: Bool)

instance (ValidConstraint c, MonadLevel m, DefaultAllowConstraints m ~ b)
          => ConstraintPassThrough c m b

instance (MonadLevel m) => ConstraintPassThrough IsBaseMonad m True
