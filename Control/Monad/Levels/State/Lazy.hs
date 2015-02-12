{- |
   Module      : Control.Monad.Levels.State.Lazy
   Description : Lazy stateful computations
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : MIT
   Maintainer  : Ivan.Miljenovic@gmail.com

Lazy stateful computations.

 -}
module Control.Monad.Levels.State.Lazy
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

import Control.Monad.Trans.State.Lazy (StateT (..))
