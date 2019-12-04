{-# language AllowAmbiguousTypes   #-}
{-# language ConstraintKinds       #-}
{-# language DataKinds             #-}
{-# language FlexibleContexts      #-}
{-# language FlexibleInstances     #-}
{-# language GADTs                 #-}
{-# language MultiParamTypeClasses #-}
{-# language OverloadedStrings     #-}
{-# language PolyKinds             #-}
{-# language ScopedTypeVariables   #-}
{-# language TypeApplications      #-}
{-# language TypeFamilies          #-}
{-# language TypeOperators         #-}
{-# language UndecidableInstances  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Mu.Adapter.ProtoBuf (
  -- * Custom annotations
  ProtoBufAnnotation(..)
  -- * Conversion using schemas
, IsProtoSchema
, HasProtoSchema
, toProtoViaSchema
, fromProtoViaSchema
, parseProtoViaSchema
  -- * Conversion using registry
, FromProtoBufRegistry
, fromProtoBufWithRegistry
, parseProtoBufWithRegistry
) where

import           Control.Applicative
import qualified Data.ByteString          as BS
import           Data.Int
import           Data.SOP                 (All)
import qualified Data.Text                as T
import qualified Data.Text.Lazy           as LT
import           GHC.TypeLits
import           Proto3.Wire
import qualified Proto3.Wire.Decode       as PBDec
import qualified Proto3.Wire.Encode       as PBEnc

import           Mu.Schema.Annotations
import           Mu.Schema.Class
import           Mu.Schema.Definition
import           Mu.Schema.Interpretation
import qualified Mu.Schema.Registry       as R

data ProtoBufAnnotation
  = ProtoBufId Nat
  | ProtoBufOneOfIds [Nat]

type family FindProtoBufId (sch :: Schema tn fn) (t :: tn) (f :: fn) where
  FindProtoBufId sch t f
    = FindProtoBufId' t f (GetFieldAnnotation (AnnotatedSchema ProtoBufAnnotation sch) t f)

type family FindProtoBufId' (t :: tn) (f :: fn) (p :: ProtoBufAnnotation) :: Nat where
  FindProtoBufId' t f ('ProtoBufId n) = n
  FindProtoBufId' t f other
    = TypeError ('Text "protocol buffers id not available for field "
                 ':<>: 'ShowType t ':<>: 'Text "/" ':<>: 'ShowType f)

type family FindProtoBufOneOfIds (sch :: Schema tn fn) (t :: tn) (f :: fn) where
  FindProtoBufOneOfIds sch t f
    = FindProtoBufOneOfIds' t f (GetFieldAnnotation (AnnotatedSchema ProtoBufAnnotation sch) t f)

type family FindProtoBufOneOfIds' (t :: tn) (f :: fn) (p :: ProtoBufAnnotation) :: [Nat] where
  FindProtoBufOneOfIds' t f ('ProtoBufOneOfIds ns) = ns
  FindProtoBufOneOfIds' t f other
    = TypeError ('Text "protocol buffers id not available for oneof field "
                 ':<>: 'ShowType t ':<>: 'Text "/" ':<>: 'ShowType f)

-- CONVERSION USING SCHEMAS

class ProtoBridgeTerm sch (sch :/: sty) => IsProtoSchema sch sty
instance ProtoBridgeTerm sch (sch :/: sty) => IsProtoSchema sch sty

type HasProtoSchema sch sty a = (HasSchema sch sty a, IsProtoSchema sch sty)

toProtoViaSchema :: forall t f (sch :: Schema t f) a sty.
                    (HasProtoSchema sch sty a)
                 => a -> PBEnc.MessageBuilder
toProtoViaSchema = termToProto . toSchema' @sch

fromProtoViaSchema :: forall t f (sch :: Schema t f) a sty.
                      (HasProtoSchema sch sty a)
                   => PBDec.Parser PBDec.RawMessage a
fromProtoViaSchema = fromSchema' @sch <$> protoToTerm

parseProtoViaSchema :: forall sch a sty.
                       (HasProtoSchema sch sty a)
                    => BS.ByteString -> Either PBDec.ParseError a
parseProtoViaSchema = PBDec.parse (fromProtoViaSchema @_ @_ @sch)

-- CONVERSION USING REGISTRY

fromProtoBufWithRegistry
  :: forall (r :: R.Registry) t.
     FromProtoBufRegistry r t
  => PBDec.Parser PBDec.RawMessage t
fromProtoBufWithRegistry = fromProtoBufRegistry' (Proxy @r)

parseProtoBufWithRegistry
  :: forall (r :: R.Registry) t.
     FromProtoBufRegistry r t
  => BS.ByteString -> Either PBDec.ParseError t
parseProtoBufWithRegistry = PBDec.parse (fromProtoBufWithRegistry @r)

class FromProtoBufRegistry (ms :: Mappings Nat Schema') t where
  fromProtoBufRegistry' :: Proxy ms -> PBDec.Parser PBDec.RawMessage t

instance FromProtoBufRegistry '[] t where
  fromProtoBufRegistry' _ = PBDec.Parser (\_ -> Left (PBDec.WireTypeError "no schema found in registry"))
instance (HasProtoSchema s sty t, FromProtoBufRegistry ms t)
         => FromProtoBufRegistry ( (n ':-> s) ': ms) t where
  fromProtoBufRegistry' _ = fromProtoViaSchema @_ @_ @s <|> fromProtoBufRegistry' (Proxy @ms)


-- =======================================
-- IMPLEMENTATION OF GENERIC SERIALIZATION
-- =======================================

instance Alternative (PBDec.Parser i) where
  empty = PBDec.Parser (\_ -> Left (PBDec.WireTypeError "cannot parse"))
  PBDec.Parser x <|> PBDec.Parser y
    = PBDec.Parser $ \i -> case x i of
                             Left _      -> y i
                             r@(Right _) -> r

-- Top-level terms
class ProtoBridgeTerm (sch :: Schema tn fn) (t :: TypeDef tn fn) where
  termToProto :: Term sch t -> PBEnc.MessageBuilder
  protoToTerm :: PBDec.Parser PBDec.RawMessage (Term sch t)

-- Embedded terms
class ProtoBridgeEmbedTerm (sch :: Schema tn fn) (t :: TypeDef tn fn) where
  termToEmbedProto :: FieldNumber -> Term sch t -> PBEnc.MessageBuilder
  embedProtoToFieldValue :: PBDec.Parser PBDec.RawField (Term sch t)
  embedProtoToOneFieldValue :: PBDec.Parser PBDec.RawPrimitive (Term sch t)

class ProtoBridgeField (sch :: Schema tn fn) (ty :: tn) (f :: FieldDef tn fn) where
  fieldToProto :: Field sch f -> PBEnc.MessageBuilder
  protoToField :: PBDec.Parser PBDec.RawMessage (Field sch f)

class ProtoBridgeFieldValue (sch :: Schema tn fn) (t :: FieldType tn) where
  fieldValueToProto :: FieldNumber -> FieldValue sch t -> PBEnc.MessageBuilder
  protoToFieldValue :: PBDec.Parser PBDec.RawField (FieldValue sch t)

class ProtoBridgeOneFieldValue (sch :: Schema tn fn) (t :: FieldType tn) where
  protoToOneFieldValue :: PBDec.Parser PBDec.RawPrimitive (FieldValue sch t)

class ProtoBridgeUnionFieldValue (ids :: [Nat]) (sch :: Schema tn fn) (ts :: [FieldType tn]) where
  unionFieldValueToProto :: NS (FieldValue sch) ts -> PBEnc.MessageBuilder
  protoToUnionFieldValue :: PBDec.Parser PBDec.RawMessage (NS (FieldValue sch) ts)

-- --------
-- TERMS --
-- --------

-- RECORDS
-- -------

instance (All (ProtoBridgeField sch name) args, ProtoBridgeFields sch name args)
         => ProtoBridgeTerm sch ('DRecord name args) where
  termToProto (TRecord fields) = go fields
    where go :: forall fs. All (ProtoBridgeField sch name) fs
             => NP (Field sch) fs -> PBEnc.MessageBuilder
          go Nil       = mempty
          go (f :* fs) = fieldToProto @_ @_ @sch @name f <> go fs
  protoToTerm = TRecord <$> protoToFields @_ @_ @sch @name

class ProtoBridgeFields (sch :: Schema tn fn) (ty :: tn) (fields :: [FieldDef tn fn]) where
  protoToFields :: PBDec.Parser PBDec.RawMessage (NP (Field sch) fields)
instance ProtoBridgeFields sch ty '[] where
  protoToFields = pure Nil
instance (ProtoBridgeField sch ty f, ProtoBridgeFields sch ty fs)
         => ProtoBridgeFields sch ty (f ': fs) where
  protoToFields = (:*) <$> protoToField @_ @_ @sch @ty <*> protoToFields @_ @_ @sch @ty

instance ProtoBridgeTerm sch ('DRecord name args)
         => ProtoBridgeEmbedTerm sch ('DRecord name args) where
  termToEmbedProto fid v = PBEnc.embedded fid (termToProto v)
  embedProtoToFieldValue = do
    t <- PBDec.embedded (protoToTerm @_ @_ @sch @('DRecord name args))
    case t of
      Nothing -> PBDec.Parser (\_ -> Left (PBDec.WireTypeError "expected message"))
      Just v  -> return v
  embedProtoToOneFieldValue = PBDec.embedded' (protoToTerm @_ @_ @sch @('DRecord name args))

-- ENUMERATIONS
-- ------------

instance TypeError ('Text "protobuf requires wrapping enums in a message")
         => ProtoBridgeTerm sch ('DEnum name choices) where
  termToProto = error "protobuf requires wrapping enums in a message"
  protoToTerm = error "protobuf requires wrapping enums in a message"

instance ProtoBridgeEnum sch name choices
         => ProtoBridgeEmbedTerm sch ('DEnum name choices) where
  termToEmbedProto fid (TEnum v) = enumToProto @_ @_ @sch @name fid v
  embedProtoToFieldValue    = do n <- PBDec.one PBDec.int32 0
                                 TEnum <$> protoToEnum @_ @_ @sch @name n
  embedProtoToOneFieldValue = do n <- PBDec.int32
                                 TEnum <$> protoToEnum @_ @_ @sch @name n

class ProtoBridgeEnum (sch :: Schema tn fn) (ty :: tn) (choices :: [ChoiceDef fn]) where
  enumToProto :: FieldNumber -> NS Proxy choices -> PBEnc.MessageBuilder
  protoToEnum :: Int32 -> PBDec.Parser a (NS Proxy choices)
instance ProtoBridgeEnum sch ty '[] where
  enumToProto = error "empty enum"
  protoToEnum _ = PBDec.Parser (\_ -> Left (PBDec.WireTypeError "unknown enum type"))
instance (KnownNat (FindProtoBufId sch ty c), ProtoBridgeEnum sch ty cs)
         => ProtoBridgeEnum sch ty ('ChoiceDef c ': cs) where
  enumToProto fid (Z _) = PBEnc.int32 fid enumValue
    where enumValue = fromIntegral (natVal (Proxy @(FindProtoBufId sch ty c)))
  enumToProto fid (S v) = enumToProto @_ @_ @sch @ty fid v
  protoToEnum n
    | n == enumValue = return (Z Proxy)
    | otherwise      = S <$> protoToEnum @_ @_ @sch @ty n
    where enumValue = fromIntegral (natVal (Proxy @(FindProtoBufId sch ty c)))

-- SIMPLE
-- ------

instance TypeError ('Text "protobuf requires wrapping primitives in a message")
         => ProtoBridgeTerm sch ('DSimple t) where
  termToProto = error "protobuf requires wrapping primitives in a message"
  protoToTerm = error "protobuf requires wrapping primitives in a message"

-- ---------
-- FIELDS --
-- ---------

instance {-# OVERLAPPABLE #-}
         (ProtoBridgeFieldValue sch t, KnownNat (FindProtoBufId sch ty name))
         => ProtoBridgeField sch ty ('FieldDef name t) where
  fieldToProto (Field v) = fieldValueToProto fieldId v
    where fieldId = fromInteger $ natVal (Proxy @(FindProtoBufId sch ty name))
  protoToField = Field <$> protoToFieldValue `at` fieldId
    where fieldId = fromInteger $ natVal (Proxy @(FindProtoBufId sch ty name))

instance {-# OVERLAPS #-}
         (ProtoBridgeUnionFieldValue (FindProtoBufOneOfIds sch ty name) sch ts)
         => ProtoBridgeField sch ty ('FieldDef name ('TUnion ts)) where
  fieldToProto (Field (FUnion v)) = unionFieldValueToProto @_ @_ @(FindProtoBufOneOfIds sch ty name) v
  protoToField = Field . FUnion <$> protoToUnionFieldValue @_ @_ @(FindProtoBufOneOfIds sch ty name)

-- ------------------
-- TYPES OF FIELDS --
-- ------------------

-- SCHEMATIC
-- ---------

instance ProtoBridgeEmbedTerm sch (sch :/: t)
         => ProtoBridgeFieldValue sch ('TSchematic t) where
  fieldValueToProto fid (FSchematic v) = termToEmbedProto fid v
  protoToFieldValue = FSchematic <$> embedProtoToFieldValue
instance ProtoBridgeEmbedTerm sch (sch :/: t)
         => ProtoBridgeOneFieldValue sch ('TSchematic t) where
  protoToOneFieldValue = FSchematic <$> embedProtoToOneFieldValue

-- PRIMITIVE TYPES
-- ---------------

instance TypeError ('Text "null cannot be converted to protobuf")
         => ProtoBridgeFieldValue sch 'TNull where
  fieldValueToProto = error "null cannot be converted to protobuf"
  protoToFieldValue = error "null cannot be converted to protobuf"
instance TypeError ('Text "null cannot be converted to protobuf")
         => ProtoBridgeOneFieldValue sch 'TNull where
  protoToOneFieldValue = error "null cannot be converted to protobuf"

instance ProtoBridgeFieldValue sch ('TPrimitive Int) where
  fieldValueToProto fid (FPrimitive n) = PBEnc.int32 fid (fromIntegral n)
  protoToFieldValue = FPrimitive . fromIntegral <$> PBDec.one PBDec.int32 0
instance ProtoBridgeOneFieldValue sch ('TPrimitive Int) where
  protoToOneFieldValue = FPrimitive . fromIntegral <$> PBDec.int32

instance ProtoBridgeFieldValue sch ('TPrimitive Int32) where
  fieldValueToProto fid (FPrimitive n) = PBEnc.int32 fid n
  protoToFieldValue = FPrimitive <$> PBDec.one PBDec.int32 0
instance ProtoBridgeOneFieldValue sch ('TPrimitive Int32) where
  protoToOneFieldValue = FPrimitive <$> PBDec.int32

instance ProtoBridgeFieldValue sch ('TPrimitive Int64) where
  fieldValueToProto fid (FPrimitive n) = PBEnc.int64 fid n
  protoToFieldValue = FPrimitive <$> PBDec.one PBDec.int64 0
instance ProtoBridgeOneFieldValue sch ('TPrimitive Int64) where
  protoToOneFieldValue = FPrimitive <$> PBDec.int64

-- WARNING! These instances may go out of bounds
instance ProtoBridgeFieldValue sch ('TPrimitive Integer) where
  fieldValueToProto fid (FPrimitive n) = PBEnc.int64 fid (fromInteger n)
  protoToFieldValue = FPrimitive . fromIntegral <$> PBDec.one PBDec.int64 0
instance ProtoBridgeOneFieldValue sch ('TPrimitive Integer) where
  protoToOneFieldValue = FPrimitive . fromIntegral <$> PBDec.int64

instance ProtoBridgeFieldValue sch ('TPrimitive Float) where
  fieldValueToProto fid (FPrimitive n) = PBEnc.float fid n
  protoToFieldValue = FPrimitive <$> PBDec.one PBDec.float 0
instance ProtoBridgeOneFieldValue sch ('TPrimitive Float) where
  protoToOneFieldValue = FPrimitive <$> PBDec.float

instance ProtoBridgeFieldValue sch ('TPrimitive Double) where
  fieldValueToProto fid (FPrimitive n) = PBEnc.double fid n
  protoToFieldValue = FPrimitive <$> PBDec.one PBDec.double 0
instance ProtoBridgeOneFieldValue sch ('TPrimitive Double) where
  protoToOneFieldValue = FPrimitive <$> PBDec.double

instance ProtoBridgeFieldValue sch ('TPrimitive Bool) where
  fieldValueToProto fid (FPrimitive n) = PBEnc.enum fid n
  protoToFieldValue = FPrimitive <$> PBDec.one PBDec.bool False
instance ProtoBridgeOneFieldValue sch ('TPrimitive Bool) where
  protoToOneFieldValue = FPrimitive <$> PBDec.bool

instance ProtoBridgeFieldValue sch ('TPrimitive T.Text) where
  fieldValueToProto fid (FPrimitive n) = PBEnc.text fid (LT.fromStrict n)
  protoToFieldValue = FPrimitive . LT.toStrict <$> PBDec.one PBDec.text ""
instance ProtoBridgeOneFieldValue sch ('TPrimitive T.Text) where
  protoToOneFieldValue = FPrimitive . LT.toStrict <$> PBDec.text

instance ProtoBridgeFieldValue sch ('TPrimitive LT.Text) where
  fieldValueToProto fid (FPrimitive n) = PBEnc.text fid n
  protoToFieldValue = FPrimitive <$> PBDec.one PBDec.text ""
instance ProtoBridgeOneFieldValue sch ('TPrimitive LT.Text) where
  protoToOneFieldValue = FPrimitive <$> PBDec.text

instance ProtoBridgeFieldValue sch ('TPrimitive BS.ByteString) where
  fieldValueToProto fid (FPrimitive n) = PBEnc.byteString fid n
  protoToFieldValue = FPrimitive <$> PBDec.one PBDec.byteString ""
instance ProtoBridgeOneFieldValue sch ('TPrimitive BS.ByteString) where
  protoToOneFieldValue = FPrimitive <$> PBDec.byteString

-- Note that Maybes and Lists require that we recur on the OneFieldValue class

instance (ProtoBridgeFieldValue sch t, ProtoBridgeOneFieldValue sch t)
         => ProtoBridgeFieldValue sch ('TOption t) where
  fieldValueToProto _   (FOption Nothing)  = mempty
  fieldValueToProto fid (FOption (Just v)) = fieldValueToProto fid v
  protoToFieldValue = FOption <$> PBDec.one (Just <$> protoToOneFieldValue) Nothing

instance TypeError ('Text "optionals cannot be nested in protobuf")
         => ProtoBridgeOneFieldValue sch ('TOption t) where
  protoToOneFieldValue = error "optionals cannot be nested in protobuf"

instance (ProtoBridgeFieldValue sch t, ProtoBridgeOneFieldValue sch t)
         => ProtoBridgeFieldValue sch ('TList t) where
  fieldValueToProto fid (FList xs) = foldMap (fieldValueToProto fid) xs
  protoToFieldValue = FList <$> PBDec.repeated protoToOneFieldValue

instance TypeError ('Text "lists cannot be nested in protobuf")
         => ProtoBridgeOneFieldValue sch ('TList t) where
  protoToOneFieldValue = error "lists cannot be nested in protobuf"

instance TypeError ('Text "maps are not currently supported")
         => ProtoBridgeFieldValue sch ('TMap k v) where
  fieldValueToProto = error "maps are not currently supported"
  protoToFieldValue = error "maps are not currently supported"

instance TypeError ('Text "nested unions are not currently supported")
         => ProtoBridgeFieldValue sch ('TUnion choices) where
  fieldValueToProto = error "nested unions are not currently supported"
  protoToFieldValue = error "nested unions are not currently supported"

-- UNIONS
-- ------

instance ProtoBridgeUnionFieldValue ids sch '[] where
  unionFieldValueToProto = error "empty list of unions"
  protoToUnionFieldValue = PBDec.Parser (\_ -> Left (PBDec.WireTypeError "unknown type in an union"))

instance ( ProtoBridgeFieldValue sch t, KnownNat thisId
         , ProtoBridgeUnionFieldValue restIds sch ts )
         => ProtoBridgeUnionFieldValue (thisId ': restIds) sch (t ': ts) where
  unionFieldValueToProto (Z v) = fieldValueToProto fieldId v
    where fieldId = fromInteger $ natVal (Proxy @thisId)
  unionFieldValueToProto (S v) = unionFieldValueToProto @_ @_ @restIds v
  protoToUnionFieldValue
    = Z <$> protoToFieldValue `at` fieldId <|> S <$> protoToUnionFieldValue @_ @_ @restIds
    where fieldId = fromInteger $ natVal (Proxy @thisId)