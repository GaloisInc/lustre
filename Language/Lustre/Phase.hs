module Language.Lustre.Phase where

import Data.Set(Set)
import qualified Data.Set as Set

data LustrePhase = PhaseRename
                 | PhaseTypecheck
                 | PhaseNoStatic
                 | PhaseNoStruct
                 | PhaseInline
                 | PhaseToCore
                   deriving (Show,Eq,Ord,Enum,Bounded)

noPhases :: Set LustrePhase
noPhases = Set.empty

allPhases :: Set LustrePhase
allPhases = Set.fromList [ minBound .. maxBound ]

phases :: [LustrePhase] -> Set LustrePhase
phases = Set.fromList

