{-# Language DataKinds, GeneralizedNewtypeDeriving #-}
-- | "Global" monad for Lustre processing.
module Language.Lustre.Monad
  ( -- * The Lustre monad
    lustreRun
  , LustreConf(..)
  , LustreM
  , lustreError
  , lustreWarning
  , lustreWarnings
  , lustreNameSeed
  , lustreSetNameSeed
  , lustreSetVerbose
  , lustreLog
    -- * Name seeds
  , NameSeed
  , nextNameSeed
  , nameSeedToInt
  , invalidNameSeed
  , isValidNameSeed
  ) where


import System.IO(Handle,hPutStrLn)
import MonadLib
import Control.Exception(throwIO)

import Language.Lustre.Error
import Language.Lustre.Panic

-- | A common monad for all lustre passes
newtype LustreM a = LustreM
  { unLustreM ::
      WithBase IO
        [ ReaderT    GlobalLustreEnv
        , ExceptionT LustreError
        , StateT     GlobalLustreState
        ] a
  } deriving (Functor,Applicative,Monad)


data GlobalLustreEnv = GlobalLustreEnv
  { luLogHandle :: !Handle
  }


-- | Generic state commong the lustre implementation
data GlobalLustreState = GlobalLustreState
  { luWarnings  :: ![LustreWarning]
  , luNameSeed  :: !NameSeed
  , luVerbose   :: !Bool
  }

-- | An abstract type for generating names.
newtype NameSeed = NameSeed Int deriving Show


-- | A new name seed.
nextNameSeed :: NameSeed -> NameSeed
nextNameSeed (NameSeed x) = NameSeed (x + 1)

-- | Name seed rendered as a number.
nameSeedToInt :: NameSeed -> Int
nameSeedToInt (NameSeed x) = x

-- | In a few places we have name seeds that should not be used.
-- To enforce this invariant, we use 'invalidNameSeeds', so that it
-- is fairly easy to notice if messed up.
-- (we cannot use 'error' as the NameSeed is strict)
invalidNameSeed :: Int -> NameSeed
invalidNameSeed x = if x < 0 then NameSeed x else NameSeed (negate x)

-- | Is this a valid name seed.
isValidNameSeed :: NameSeed -> Bool
isValidNameSeed (NameSeed x) = x >= 0

-- | Configuration for running Lustre computations.
data LustreConf = LustreConf
  { lustreInitialNameSeed :: Maybe NameSeed
  , lustreLogHandle       :: !Handle
  }

-- | Execute a Lustre computation.
-- May throw `LustreError`
lustreRun :: LustreConf -> LustreM a -> IO a
lustreRun conf m =
  do let env = GlobalLustreEnv { luLogHandle = lustreLogHandle conf }
         st  = GlobalLustreState
                 { luNameSeed = case lustreInitialNameSeed conf of
                                  Nothing -> NameSeed 0
                                  Just s  -> s
                 , luVerbose  = False
                 , luWarnings = []
                 }
     (res,_) <- runM (unLustreM m) env st
     case res of
       Left err -> throwIO err
       Right a  -> pure a

-- | Log something, if we are verbose.
lustreLog :: String -> LustreM ()
lustreLog msg =
  LustreM $ do verb <- luVerbose <$> get
               when verb $
                  do h <- luLogHandle <$> ask
                     inBase (hPutStrLn h msg)

lustreSetVerbose :: Bool -> LustreM ()
lustreSetVerbose b = LustreM $ sets_ $ \s -> s { luVerbose = b }

-- | Abort further computation with the given error.
lustreError :: LustreError -> LustreM a
lustreError e = LustreM (raise e)

-- | Record a warning.
lustreWarning :: LustreWarning -> LustreM ()
lustreWarning w =
  LustreM $ sets_ $ \s -> s { luWarnings = w : luWarnings s }

-- | Get the warnings collected so far.
lustreWarnings :: LustreM [LustreWarning]
lustreWarnings = LustreM $ luWarnings <$> get

-- | Get the current name seed.
lustreNameSeed :: LustreM NameSeed
lustreNameSeed = LustreM $ luNameSeed <$> get

-- | Set the current name seed to something.
lustreSetNameSeed :: NameSeed -> LustreM ()
lustreSetNameSeed newSeed =
  LustreM $ sets_ $ \s ->
    let oldSeed = luNameSeed s
    in if nameSeedToInt oldSeed > nameSeedToInt newSeed
         then panic "Language.Lustre.Monad.lustreSetSeed"
                [ "New seed is smaller than the current seed."
                , "*** Old seed: " ++ show oldSeed
                , "*** New seed: " ++ show newSeed
                ]
         else s { luNameSeed = newSeed }


