{- |
   Module      : Control.Monad.Levels.RWS.Lazy
   Description : Lazy monad with reader, writer and state abilities
   Copyright   : (c) Ivan Lazar Miljenovic
   License     : MIT
   Maintainer  : Ivan.Miljenovic@gmail.com

Note that the original definitions are used for the various reader,
writer and state computations: as such, if there is (for example)
another level that satisfies 'IsReader r' above the one that satisfies
'IsRWS r w s' in the stack, then calling 'ask' will use the higher
level.

 -}
module Control.Monad.Levels.RWS.Lazy
  ( RWST(..)
  , module Control.Monad.Levels.RWS
  ) where

import Control.Monad.Levels.RWS

import Control.Monad.Trans.RWS.Lazy
