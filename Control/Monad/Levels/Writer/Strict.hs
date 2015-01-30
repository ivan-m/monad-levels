{- |
   Module      : Control.Monad.Levels.Writer.Strict
   Description : Strict writer monad
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : 3-Clause BSD-style
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Control.Monad.Levels.Writer.Strict
  ( writer
  , tell
  , HasWriter
  , listen
  , CanListen
  , ListenFn
  , pass
  , CanPass
  , PassFn
  , WriterT(..)
  , IsWriter
  ) where

import Control.Monad.Levels.Writer
import Control.Monad.Trans.Writer.Strict (WriterT (..))
