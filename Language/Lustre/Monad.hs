{-# Language DataKinds, GeneralizedNewtypeDeriving #-}
{-# Language MultiParamTypeClasses #-}
-- | "Global" monad for Lustre processing.
module Language.Lustre.Monad
  ( -- * The Lustre monad
    runLustre
  , LustreConf(..)
  , LustreM

    -- ** Errors and Warnings
  , reportError
  , addWarning
  , getWarnings
  , LustreError(..)
  , LustreWarning(..)

    -- ** Access to the Name Seed
  , getNameSeed
  , setNameSeed
  , newInt

    -- ** Logging
  , setVerbose
  , logMessage

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

instance BaseM LustreM LustreM where
  inBase = id


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
runLustre :: LustreConf -> LustreM a -> IO a
runLustre conf m =
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
logMessage :: String -> LustreM ()
logMessage msg =
  LustreM $ do verb <- luVerbose <$> get
               when verb $
                  do h <- luLogHandle <$> ask
                     inBase (hPutStrLn h msg)

-- | Set verbosity. 'True' means enable logging.  Affect `lustreLog`.
setVerbose :: Bool -> LustreM ()
setVerbose b = LustreM $ sets_ $ \s -> s { luVerbose = b }

-- | Abort further computation with the given error.
reportError :: LustreError -> LustreM a
reportError e = LustreM (raise e)

-- | Record a warning.
addWarning :: LustreWarning -> LustreM ()
addWarning w =
  LustreM $ sets_ $ \s -> s { luWarnings = w : luWarnings s }

-- | Get the warnings collected so far.
getWarnings :: LustreM [LustreWarning]
getWarnings = LustreM $ luWarnings <$> get

-- | Get the current name seed.
getNameSeed :: LustreM NameSeed
getNameSeed = LustreM $ luNameSeed <$> get

-- | Set the current name seed to something.
setNameSeed :: NameSeed -> LustreM ()
setNameSeed newSeed =
  LustreM $ sets_ $ \s ->
    let oldSeed = luNameSeed s
    in if nameSeedToInt oldSeed > nameSeedToInt newSeed
         then panic "Language.Lustre.Monad.lustreSetSeed"
                [ "New seed is smaller than the current seed."
                , "*** Old seed: " ++ show oldSeed
                , "*** New seed: " ++ show newSeed
                ]
         else s { luNameSeed = newSeed }


-- | Use the name see to generate a new int.
newInt :: LustreM Int
newInt =
  do seed <- getNameSeed
     unless (isValidNameSeed seed) $
       panic "newName" [ "Attempt ot generate a new name in invald context."
                       , "*** Name seed hint: " ++ show seed
                       ]
     setNameSeed (nextNameSeed seed)
     pure (nameSeedToInt seed)

