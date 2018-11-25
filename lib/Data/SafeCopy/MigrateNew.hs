{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Data.SafeCopy.MigrateNew
(
    SCRecord(..),
    SetVersion, SetBase, setBase,
    ToSCRecord, toSCRecord,
    fromSCRecord,
    WithField, addField,
    WithoutField, removeField,
)
where

import BasePrelude

import SuperRecord
import Data.SafeCopy
import GHC.TypeLits
import GHC.Generics
import GHC.Exts
import GHC.ST
import Data.Serialize (Put, Get)

----------------------------------------------------------------------------
-- Type
----------------------------------------------------------------------------

-- | A generic record type with a 'SafeCopy' instance.
--
-- Any simple Haskell record type can be converted into 'SCRecord'. From
-- there, we can establish a chain of migrations, where every previous
-- version of a datatype is derived by doing modifications ('WithField' or
-- 'WithoutField') on a more recent version.
newtype SCRecord (version :: Nat) (base :: Bool) (fields :: [*]) =
    SCRecord (Record fields)

----------------------------------------------------------------------------
-- Setters
----------------------------------------------------------------------------

-- | Specify the version of the datatype.
type family SetVersion (version :: Nat) record where
    SetVersion version (SCRecord _ base fields) = SCRecord version base fields

-- | Specify that the datatype is the "base" (i.e. the first version,
-- regardless of what the number actually is).
type family SetBase record where
    SetBase (SCRecord version _ fields) = SCRecord version 'True fields

setBase :: SCRecord version 'False fields -> SCRecord version 'True fields
setBase (SCRecord r) = SCRecord r

----------------------------------------------------------------------------
-- Conversion to and from native records
----------------------------------------------------------------------------

-- | Convert a native Haskell record to an 'SCRecord' (type-level).
type ToSCRecord (version :: Nat) (a :: *) =
    SCRecord version 'False (FromNative (Rep a))

-- | Convert a native Haskell record to an 'SCRecord' (value-level).
toSCRecord
    :: ( fields ~ FromNative (Rep a)
       , sortedFields ~ Sort fields
       , RecSize fields ~ s
       , KnownNat s
       , Generic a
       , HasFromNative (Rep a)
       , RecCopy fields fields sortedFields
       )
    => a -> ToSCRecord version a
toSCRecord = SCRecord . rsort . fromNative

-- | Convert an 'SCRecord' to a native Haskell record (value-level).
fromSCRecord
    :: ( ToNative (Rep a) sortedFields
       , sortedFields ~ Sort fields
       , Generic a
       )
    => SCRecord version base fields
    -> a
fromSCRecord (SCRecord r) = toNative r

----------------------------------------------------------------------------
-- Adding fields
----------------------------------------------------------------------------

-- | Add a field to a record (type-level).
type family WithField label field record where
    WithField label field (SCRecord version base fields) =
        SCRecord version base ((label := field) ': Sort fields)

-- | Add a field to a record (value-level).
addField
    :: ( KnownSymbol label
       , sortedFields ~ Sort fields
       , RecSize sortedFields ~ s
       , fields' ~ Sort ((label := field) ': sortedFields)
       , KnownNat s
       , KnownNat (RecVecIdxPos label fields')
       , KeyDoesNotExist label sortedFields
       , RecCopy sortedFields sortedFields fields'
       )
    => FldProxy label
    -> field
    -> SCRecord version base fields
    -> WithField label field (SCRecord version base fields)
addField label field (SCRecord r) = SCRecord (rcons (label := field) r)

-- | Remove a field from a record (type-level).
type family WithoutField label record where
    WithoutField label (SCRecord version base fields) =
        SCRecord version base (RemoveAccessTo label (Sort fields))

----------------------------------------------------------------------------
-- Removing fields
----------------------------------------------------------------------------

-- | Remove a field from a record (value-level).
removeField
    :: ( KnownSymbol label
       , sortedFields ~ Sort fields
       , RecSize sortedFields ~ s
       , fields' ~ Sort (RemoveAccessTo label sortedFields)
       , KnownNat s
       , KnownNat (RecTyIdxH 0 label sortedFields)
       , RecCopy sortedFields sortedFields fields'
       )
    => FldProxy label
    -> SCRecord version base fields
    -> WithoutField label (SCRecord version base fields)
removeField label (SCRecord r) = SCRecord (rdelete label r)

----------------------------------------------------------------------------
-- SafeCopy instances
----------------------------------------------------------------------------

instance ( sortedFields ~ Sort fields
         , RecApply sortedFields sortedFields SafeCopy
         , RecGetCopy sortedFields
         , KnownNat (RecSize fields)
         , KnownNat version
         )
      => SafeCopy (SCRecord version 'True fields) where
    version = fromInteger (natVal (Proxy @version))
    kind = base
    putCopy = genericPutCopy
    getCopy = genericGetCopy

instance ( sortedFields ~ Sort fields
         , RecApply sortedFields sortedFields SafeCopy
         , RecGetCopy sortedFields
         , KnownNat (RecSize fields)
         , Migrate (SCRecord version 'False fields)
         , KnownNat version
         )
      => SafeCopy (SCRecord version 'False fields) where
    version = fromInteger (natVal (Proxy @version))
    kind = extension
    putCopy = genericPutCopy
    getCopy = genericGetCopy

genericPutCopy
    :: ( sortedFields ~ Sort fields
       , RecApply sortedFields sortedFields SafeCopy
       )
    => SCRecord version base fields -> Contained Put
genericPutCopy (SCRecord r) =
    contain $ sequence_ $
    reflectRec @SafeCopy Proxy (\_ v -> safePut v) r

genericGetCopy
    :: forall version base fields sortedFields s .
       ( sortedFields ~ Sort fields
       , s ~ RecSize fields
       , RecGetCopy sortedFields
       , KnownNat s
       )
    => Contained (Get (SCRecord version base fields))
genericGetCopy = contain $ fmap SCRecord $
    recGetCopy @sortedFields (fromIntegral (natVal (Proxy @s)))

-- | Machinery to implement 'genericGetCopy'
class RecGetCopy (fields :: [*]) where
    recGetCopy :: Int -> Get (Rec fields)

instance RecGetCopy '[] where
    recGetCopy initSize = pure (unsafeRNil initSize)

instance ( KnownSymbol l, SafeCopy t, RecGetCopy fields
         , RecSize fields ~ s, KnownNat s, KeyDoesNotExist l fields
         )
      => RecGetCopy ((l := t) ': fields) where
    recGetCopy initSize = do
        let lbl = FldProxy @l
        v <- safeGet @t
        rest <- recGetCopy initSize
        pure $ unsafeRCons (lbl := v) rest

----------------------------------------------------------------------------
-- SuperRecord utilities
----------------------------------------------------------------------------

-- | Delete a field from a record.
rdelete ::
    forall l lts s sortedLts.
    ( RecSize lts ~ s
    , sortedLts ~ Sort (RemoveAccessTo l lts)
    , KnownNat s
    , KnownNat (RecTyIdxH 0 l lts)
    , RecCopy lts lts sortedLts
    )
    => FldProxy l -> Rec lts -> Rec sortedLts
rdelete _ lts =
    runST' $ ST $ \s# ->
    case newSmallArray# newSize# (error "No value") s# of
      (# s'#, arr# #) ->
          case recCopyInto (Proxy :: Proxy lts) lts (Proxy :: Proxy sortedLts) arr# s'# of
            s''# ->
                  case unsafeFreezeSmallArray# arr# s''# of
                    (# s'''#, a# #) -> (# s'''#, Rec a# #)
    where
        newSize# = size# -# 1#
        !(I# size#) = fromIntegral $ natVal' (proxy# :: Proxy# s)
{-# INLINE rdelete #-}

-- | Sort a record.
rsort ::
    forall lts s sortedLts.
    ( RecSize lts ~ s
    , sortedLts ~ Sort lts
    , KnownNat s
    , RecCopy lts lts sortedLts
    )
    => Rec lts -> Rec sortedLts
rsort lts =
    runST' $ ST $ \s# ->
    case newSmallArray# size# (error "No value") s# of
      (# s'#, arr# #) ->
          case recCopyInto (Proxy :: Proxy lts) lts (Proxy :: Proxy sortedLts) arr# s'# of
            s''# ->
                  case unsafeFreezeSmallArray# arr# s''# of
                    (# s'''#, a# #) -> (# s'''#, Rec a# #)
    where
        !(I# size#) = fromIntegral $ natVal' (proxy# :: Proxy# s)
{-# INLINE rsort #-}

runST' :: (forall s. ST s a) -> a
runST' !s = runST s
