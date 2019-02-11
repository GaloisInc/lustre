{-# Language OverloadedStrings #-}
module Language.Lustre.Error where

import Text.PrettyPrint hiding ((<>))
import qualified Text.PrettyPrint as PP
import Control.Exception

import Language.Lustre.AST(range)
import Language.Lustre.Name
import Language.Lustre.Pretty


data LustreError =
    ResolverError ResolverError
  | TCError Doc   -- ^ XXX
    deriving Show

instance Exception LustreError

data LustreWarning =
    ResolverWarning ResolverWarning


-- | Various things that can go wrong when resolving names.
data ResolverError =
    InvalidConstantExpression String
  | UndefinedName Name
  | AmbiguousName Name OrigName OrigName
  | RepeatedDefinitions [OrigName]
  | BadRecursiveDefs [OrigName]
    deriving Show

-- | Potential problems, but not fatal.
data ResolverWarning =
    Shadows OrigName OrigName

--------------------------------------------------------------------------------

instance Pretty ResolverError where
  ppPrec _ err =
    case err of

      InvalidConstantExpression x ->
        "Construct" <+> backticks (text x) <+>
          "may not appear in constant expressions."

      UndefinedName x ->
        located (range x)
          [ "The name" <+> backticks (pp x) <+> "is undefined." ]

      AmbiguousName x a b ->
        located (range x)
            [ "The name" <+> backticks (pp x) <+> "is ambiguous."
            , block "It may refer to:" [ppOrig a, ppOrig b]
            ]

      RepeatedDefinitions xs ->
        block "Multiple declaratoins for the same name:" (map ppOrig xs)

      BadRecursiveDefs xs ->
        block "Invalid recursive declarations:" (map ppOrig xs)

    where
    block x ys = nested x (bullets ys)
    located r xs = block ("At" <+> pp r) xs

ppOrig :: OrigName -> Doc
ppOrig x = backticks (pp x) PP.<> ","
                <+> "defined at" <+> pp (identRange (rnIdent x))


instance Pretty ResolverWarning where
  ppPrec _ warn =
    case warn of
      Shadows x y ->
        ppOrig x <+> "shadows" <+> ppOrig y



