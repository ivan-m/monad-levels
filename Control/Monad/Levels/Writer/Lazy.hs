{- |
   Module      : Control.Monad.Levels.Writer.Lazy
   Description : Lazy writer monad
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : MIT
   Maintainer  : Ivan.Miljenovic@gmail.com



 -}
module Control.Monad.Levels.Writer.Lazy
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
import Control.Monad.Trans.Writer.Lazy (WriterT (..))
