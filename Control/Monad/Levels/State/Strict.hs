{- |
   Module      : Control.Monad.Levels.State.Strict
   Description : Strict stateful computations
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : 3-Clause BSD-style
   Maintainer  : Ivan.Miljenovic@gmail.com

Strict stateful computations.

 -}
module Control.Monad.Levels.State.Strict
  ( state
  , get
  , gets
  , put
  , modify
  , modify'
  , StateT(..)
  , HasState
  , IsState
  ) where

import Control.Monad.Levels.State

import Control.Monad.Trans.State.Strict (StateT (..))
