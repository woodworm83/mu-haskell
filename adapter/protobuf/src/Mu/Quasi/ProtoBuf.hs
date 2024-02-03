{-# language CPP               #-}
{-# language DataKinds         #-}
{-# language LambdaCase        #-}
{-# language NamedFieldPuns    #-}
{-# language OverloadedStrings #-}
{-# language TemplateHaskell   #-}
{-# language ViewPatterns      #-}
{-|
Description : Quasi-quoters for Protocol Buffers schemas

Read @.proto@ files as a 'Mu.Schema.Definition.Schema'.
If you want to get the service definitions too,
you should use 'Mu.Quasi.GRpc' instead.
-}
module Mu.Quasi.ProtoBuf (
  -- * Quasi-quoters for @.proto@ files
    protobuf
  -- * Only for internal use
  , protobufToDecls
  , loadImports
  ) where

import           Control.Monad                   (foldM, when)
import           Control.Monad.IO.Class
import qualified Data.ByteString                 as B
import           Data.Int
import qualified Data.List                       as L
import           Data.List.NonEmpty              (NonEmpty (..), toList)
import qualified Data.Map.Strict                 as M
import qualified Data.Text                       as T
import           Data.Word
import           Language.Haskell.TH
import           Language.ProtocolBuffers.Parser
import qualified Language.ProtocolBuffers.Types  as P
import           System.FilePath                 (takeDirectory, (</>))

import           Mu.Adapter.ProtoBuf
import           Mu.Schema.Annotations
import           Mu.Schema.Definition

-- | Reads a @.proto@ file and generates a 'Mu.Schema.Definition.Schema'
--   with all the message types, using the name given
--   as first argument.
protobuf :: String -> FilePath -> Q [Dec]
protobuf schemaName fp
  = do r <- liftIO $ parseProtoBufFile fp
       case r of
         Left e
           -> fail ("could not parse protocol buffers spec: " ++ show e)
         Right p
           -> protobufToDecls schemaName p =<< loadImports fp p

loadImports :: FilePath -> P.ProtoBuf -> Q [P.ProtoBuf]
loadImports rootFp p = M.elems <$> loadImports' M.empty rootFp p
  where
    loadImports' :: M.Map FilePath P.ProtoBuf -> FilePath -> P.ProtoBuf -> Q (M.Map FilePath P.ProtoBuf)
    loadImports' m fp p' = foldM (loadImport fp) m $ P.imports p'
    loadImport :: FilePath -> M.Map FilePath P.ProtoBuf -> (P.ImportType, T.Text) -> Q (M.Map FilePath P.ProtoBuf)
    loadImport parentFp m (_, relFP) = do
      let fp = takeDirectory parentFp </> T.unpack relFP
      if fp `M.member` m
        then pure m
        else do
          r <- liftIO $ parseProtoBufFile fp
          case r of
            Left e -> do
              reportError $ "Include " <> fp <> " of " <> parentFp <> " not found: " <> show e
              pure m
            Right proto -> loadImports' (M.insert fp proto m) fp proto

-- | Shared portion of Protocol Buffers and gRPC quasi-quoters.
protobufToDecls :: String -> P.ProtoBuf -> [P.ProtoBuf] -> Q [Dec]
protobufToDecls schemaName p imps
  = do let schemaName' = mkName schemaName
       (schTy, annTy) <- schemaFromProtoBuf p imps
       schemaDec <- tySynD schemaName' [] (pure schTy)
#if MIN_VERSION_template_haskell(2,15,0)
       annDec <- tySynInstD (tySynEqn Nothing
                               [t| AnnotatedSchema ProtoBufAnnotation $(conT schemaName') |]
                               (pure annTy))
#else
       annDec <- tySynInstD ''AnnotatedSchema
                   (tySynEqn [ [t| ProtoBufAnnotation |], conT schemaName' ] (pure annTy))
#endif
       pure [schemaDec, annDec]

schemaFromProtoBuf :: P.ProtoBuf -> [P.ProtoBuf] -> Q (Type, Type)
schemaFromProtoBuf P.ProtoBuf {P.types = tys} imps = do
  let decls = flattenDecls (("", tys) :| []) tys <> flattenImportDecls imps
  (schTys, anns) <- unzip <$> mapM (pbTypeDeclToType $ shouldOptional decls) decls
  pure (typesToList schTys, typesToList (concat anns))
  where
    shouldOptional :: [P.TypeDeclaration] -> P.TypeName -> Bool
    shouldOptional [] this = error $ T.unpack $ "no declaration for type " <> T.intercalate "." this
    shouldOptional (P.DMessage nm _ _ _ _ : _) this
      | nm == last this = True
    shouldOptional (P.DEnum nm _ _ : _) this
      | nm == last this = False
    shouldOptional (_ : rest) this
      = shouldOptional rest this

flattenImportDecls :: [P.ProtoBuf] -> [P.TypeDeclaration]
flattenImportDecls = concatMap flattenImportDecls'
  where
    flattenImportDecls' :: P.ProtoBuf -> [P.TypeDeclaration]
    flattenImportDecls' P.ProtoBuf { P.types = tys, P.package = getPackageName -> pkg } =
      flattenDecls ((pkg, tys) :| []) tys
    getPackageName :: Maybe P.FullIdentifier -> T.Text
    getPackageName = maybe "" (T.intercalate ".")

flattenDecls :: NonEmpty (P.Identifier, [P.TypeDeclaration]) -> [P.TypeDeclaration] -> [P.TypeDeclaration]
flattenDecls (currentScope :| higherScopes) = concatMap flattenDecl
  where
    flattenDecl (P.DEnum name o f) = [P.DEnum (prependCurrentScope name) o f]
    flattenDecl (P.DMessage name o r fs decls) =
      let newScopeName = prependCurrentScope name
          newScopes = (newScopeName, decls) :| (currentScope : higherScopes)
      in P.DMessage newScopeName o r (scopeFieldType (toList newScopes) <$> fs) [] : flattenDecls newScopes decls

    scopeFieldType scopes (P.NormalField frep ftype fname fnum fopts) =
      P.NormalField frep (qualifyType scopes ftype) fname fnum fopts
    scopeFieldType scopes (P.OneOfField fname fields) = P.OneOfField fname (scopeFieldType scopes <$> fields)
    scopeFieldType scopes (P.MapField fkey fval fname fnumber fopts) =
      P.MapField (qualifyType scopes fkey) (qualifyType scopes fval) fname fnumber fopts

    qualifyType scopes (P.TOther ts) = P.TOther (qualifyTOther scopes ts)
    qualifyType _scopes t            = t

    qualifyTOther _ [] = error "This shouldn't be possible"
    qualifyTOther [] ts = [T.intercalate "." ts]
    qualifyTOther ((scopeName, decls) : rest) ts =
      if L.any (hasDeclFor ts) decls
      then [qualifyName scopeName ts]
      else qualifyTOther rest ts
      where
        qualifyName "" ts' = T.intercalate "." ts'
        qualifyName sn ts'=qualifyName "" (sn:ts')

    hasDeclFor [] _ = True
    hasDeclFor [t] (P.DEnum enumName _ _) = t == enumName
    hasDeclFor (_:_:_) P.DEnum{} = False
    hasDeclFor (t:ts) (P.DMessage msgName _ _ _ rest) =
      let nameMatch = t == msgName
          -- 'L.any' returns 'False' if 'rest' is empty, hence the 'null ts'
          -- check is required.
          restMatch = null ts || L.any (hasDeclFor ts) rest
      in nameMatch && restMatch

    prependCurrentScope x =
      case fst currentScope of
        "" -> x
        sn -> sn <> "." <> x

pbTypeDeclToType :: (P.TypeName -> Bool) -> P.TypeDeclaration -> Q (Type, [Type])
pbTypeDeclToType _ (P.DEnum name _ fields) = do
  (tys, anns) <- unzip <$> mapM pbChoiceToType fields
  (,) <$> [t|'DEnum $(textToStrLit name) $(pure $ typesToList tys)|] <*> pure anns
  where
    pbChoiceToType :: P.EnumField -> Q (Type, Type)
    pbChoiceToType (P.EnumField nm number _)
      = (,) <$> [t|'ChoiceDef $(textToStrLit nm) |]
            <*> [t|'AnnField $(textToStrLit name) $(textToStrLit nm) ('ProtoBufId $(intToLit number) '[]) |]
pbTypeDeclToType shouldOptional (P.DMessage name _ _ fields _) = do
  (tys, anns) <- unzip <$> mapM pbMsgFieldToType fields
  (,) <$> [t|'DRecord $(textToStrLit name) $(pure $ typesToList tys)|] <*> pure anns
  where
    pbMsgFieldToType :: P.MessageField -> Q (Type, Type)
    -- If we have a field type which is not primitive,
    -- it's possible to distinguish whether it's missing on wire
    -- or should be set to the default, so use Option
    -- +info -> https://github.com/higherkindness/mu-haskell/pull/130#issuecomment-596433307
    pbMsgFieldToType (P.NormalField P.Single ty@(P.TOther innerTy) nm n opts)
        | shouldOptional innerTy =
        (,) <$> [t| 'FieldDef $(textToStrLit nm) ('TOption $(pbFieldTypeToType ty)) |]
            <*> [t| 'AnnField $(textToStrLit name) $(textToStrLit nm) ('ProtoBufId $(intToLit n) $(typesToList <$> mapM pbOption opts)) |]
        | otherwise =
        (,) <$> [t| 'FieldDef $(textToStrLit nm) $(pbFieldTypeToType ty) |]
            <*> [t| 'AnnField $(textToStrLit name) $(textToStrLit nm) ('ProtoBufId $(intToLit n) $(typesToList <$> mapM pbOption opts)) |]
    pbMsgFieldToType (P.NormalField P.Single ty nm n opts) =
        (,) <$> [t| 'FieldDef $(textToStrLit nm) $(pbFieldTypeToType ty) |]
            <*> [t| 'AnnField $(textToStrLit name) $(textToStrLit nm) ('ProtoBufId $(intToLit n) $(typesToList <$> mapM pbOption opts)) |]
    pbMsgFieldToType (P.NormalField P.Repeated ty nm n opts) =
        (,) <$> [t| 'FieldDef $(textToStrLit nm) ('TList $(pbFieldTypeToType ty)) |]
            <*> [t| 'AnnField $(textToStrLit name) $(textToStrLit nm) ('ProtoBufId $(intToLit n) $(typesToList <$> mapM pbOption opts)) |]
    pbMsgFieldToType (P.MapField k v nm n opts) =
        (,) <$> [t| 'FieldDef $(textToStrLit nm) ('TMap $(pbFieldTypeToType k) $(pbFieldTypeToType v)) |]
            <*> [t| 'AnnField $(textToStrLit name) $(textToStrLit nm) ('ProtoBufId $(intToLit n) $(typesToList <$> mapM pbOption opts)) |]
    pbMsgFieldToType (P.OneOfField nm vs)
      | not (all hasFieldNumber vs)
      = fail "nested oneof fields are not supported"
      | otherwise
      = (,) <$> [t| 'FieldDef $(textToStrLit nm) ('TUnion $(typesToList <$> mapM pbOneOfFieldToType vs )) |]
            <*> [t| 'AnnField $(textToStrLit name) $(textToStrLit nm)
                       ('ProtoBufOneOfIds $(typesToList <$> mapM (intToLit . getFieldNumber) vs )) |]

    pbFieldTypeToType :: P.FieldType -> Q Type
    pbFieldTypeToType P.TInt32     = [t|'TPrimitive Int32|]
    pbFieldTypeToType P.TUInt32    = [t|'TPrimitive Word32|]
    pbFieldTypeToType P.TSInt32    = [t|'TPrimitive Int32|]
    pbFieldTypeToType P.TInt64     = [t|'TPrimitive Int64|]
    pbFieldTypeToType P.TUInt64    = [t|'TPrimitive Word64|]
    pbFieldTypeToType P.TSInt64    = [t|'TPrimitive Int64|]
    pbFieldTypeToType P.TFixed32   = fail "fixed integers are not currently supported"
    pbFieldTypeToType P.TFixed64   = fail "fixed integers are not currently supported"
    pbFieldTypeToType P.TSFixed32  = fail "fixed integers are not currently supported"
    pbFieldTypeToType P.TSFixed64  = fail "fixed integers are not currently supported"
    pbFieldTypeToType P.TDouble    = [t|'TPrimitive Double|]
    pbFieldTypeToType P.TBool      = [t|'TPrimitive Bool|]
    pbFieldTypeToType P.TString    = [t|'TPrimitive T.Text|]
    pbFieldTypeToType P.TBytes     = [t|'TPrimitive B.ByteString|]
    pbFieldTypeToType (P.TOther t) = [t|'TSchematic $(textToStrLit (T.intercalate "." t))|]

    hasFieldNumber P.NormalField {} = True
    hasFieldNumber P.MapField {}    = True
    hasFieldNumber _                = False

    getFieldNumber (P.NormalField _ _ _ n _) = n
    getFieldNumber (P.MapField    _ _ _ n _) = n
    getFieldNumber _                         = error "this should never happen"

    pbOneOfFieldToType (P.NormalField P.Single ty _ _ _)
      = pbFieldTypeToType ty
    pbOneOfFieldToType (P.NormalField P.Repeated ty _ _ _)
      = [t| 'TList $(pbFieldTypeToType ty) |]
    pbOneOfFieldToType (P.MapField k v _ _ _)
      = [t| 'TMap $(pbFieldTypeToType k) $(pbFieldTypeToType v) |]
    pbOneOfFieldToType _ = error "this should never happen"

    pbOption (P.Option oname val)
      = do when (oname == ["default"])
                (reportError "mu-protobuf does not (yet) support default values")
           [t| '( $(textToStrLit (T.intercalate "." oname))
                , $(pbConstantToOption val) ) |]

    pbConstantToOption (P.KIdentifier names)
      = [t| 'ProtoBufOptionConstantOther $(textToStrLit (T.intercalate "." names)) |]
    pbConstantToOption (P.KInt n)
      = [t| 'ProtoBufOptionConstantInt $(intToLit (fromInteger n)) |]
    pbConstantToOption (P.KBool True)
      = [t| 'ProtoBufOptionConstantBool 'True |]
    pbConstantToOption (P.KBool False)
      = [t| 'ProtoBufOptionConstantBool 'False |]
    pbConstantToOption (P.KString s)
      = [t| 'ProtoBufOptionConstantOther $(textToStrLit s) |]
    pbConstantToOption (P.KFloat s)
      = [t| 'ProtoBufOptionConstantOther $(textToStrLit (T.pack (show s))) |]
    pbConstantToOption (P.KObject s)
      = [t| 'ProtoBufOptionConstantObject
            $(typesToList <$> mapM (\(n, o) -> [t| '( $(textToStrLit n), $(pbConstantToOption o) ) |] ) s ) |]

typesToList :: [Type] -> Type
typesToList = foldr (AppT . AppT PromotedConsT) PromotedNilT

textToStrLit :: T.Text -> Q Type
textToStrLit s = pure $ LitT $ StrTyLit $ T.unpack s

intToLit :: Int -> Q Type
intToLit n = pure $ LitT $ NumTyLit $ toInteger n
