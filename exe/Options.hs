module Options where

import SimpleGetOpt
import Data.Set(Set)
import qualified Data.Set as Set

import Language.Lustre.Phase

data Options = Options
  { progFile  :: Maybe FilePath
  , inputFile :: Maybe FilePath
  , logFile   :: Maybe FilePath
  , dumpAfter :: Set LustrePhase
  , dumpState :: Bool
  , showHelp  :: Bool
  }

defaultOptions :: Options
defaultOptions = Options
  { progFile    = Nothing
  , inputFile   = Nothing
  , logFile     = Nothing
  , dumpAfter   = noPhases
  , dumpState   = False
  , showHelp    = False
  }

options :: OptSpec Options
options = OptSpec
  { progDefaults = defaultOptions
  , progOptions =

      [ Option [] ["input"]
        "Read inputs from this file (default `stdin`)."
        $ ReqArg "FILE" $ \a s ->
            case inputFile s of
              Nothing -> Right s { inputFile = Just a }
              Just _  -> Left "Multiple input files."

      , Option [] ["logFile"]
        "Write messages to his file (default `stdout`)."
        $ ReqArg "FILE" $ \a s ->
            case logFile s of
              Nothing -> Right s { logFile = Just a }
              Just _  -> Left "Multiple log file."

      , Option [] ["dump-all"]
        "Dump AST after each phase."
        $ NoArg $ \s -> Right s { dumpAfter = allPhases }

      , dumpOpt PhaseRename    "renamed"     "renaming"
      , dumpOpt PhaseTypecheck "typechecked" "type checking"
      , dumpOpt PhaseNoStatic  "no-static"   "elimininating constants"
      , dumpOpt PhaseNoStruct  "no-struct"   "elimininating strucutred data"
      , dumpOpt PhaseInline    "inlined"     "inlining nodes"
      , dumpOpt PhaseToCore    "core"        "translating to core"

      , Option [] ["dump-state"]
        "Dump state before each step."
        $ NoArg $ \s -> Right s { dumpState = True }

      , Option [] ["help"]
        "Show this helps message."
        $ NoArg $ \s -> Right s { showHelp = True }

      ]

  , progParamDocs = [("FILE", "Lustre file containing model (required).")]
  , progParams = \a s -> case progFile s of
                           Nothing -> Right s { progFile = Just a }
                           _ -> Left "Multiple program files."
  }

  where
  dumpOpt ph o msg =
    Option [] ["dump-" ++ o]
    ("Dump AST after " ++  msg ++ ".")
    $ NoArg $ \s -> Right s { dumpAfter = Set.insert ph (dumpAfter s) }

