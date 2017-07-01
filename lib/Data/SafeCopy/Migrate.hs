{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- Hack for bug in older Cabal versions
#ifndef MIN_VERSION_template_haskell
#define MIN_VERSION_template_haskell(x,y,z) 1
#endif


-- | This is a mess, sorry. This code was extracted from another project.
--
-- Currently 'changelog' is the most useful function here – see its
-- description for an example.
module Data.SafeCopy.Migrate
(
  -- * Migration for records
  deriveSafeCopySorted,
  Change(..),
  changelog,
  hs,

  -- * Migration for constructors
  GenConstructor(..),
  genVer,
  MigrateConstructor(..),
  migrateVer,

  -- * Utilities
  TypeVersion(..),
)
where


import BasePrelude hiding (Version)
import Data.Serialize (getWord8, putWord8, label)
import Data.SafeCopy
import qualified Data.SafeCopy.Internal as S
import Language.Haskell.TH.Syntax as TH
import Language.Haskell.TH.Quote
#if MIN_VERSION_template_haskell(2,8,0)
import Language.Haskell.TH hiding (Kind)
#else
import Language.Haskell.TH hiding (Kind(..))
#endif
import Language.Haskell.Meta (parseExp)
import qualified Data.Map as M
import Data.Map (Map)
import Lens.Micro
import Control.Monad.Extra
import Data.Generics.Uniplate.Data (transform)
import Data.List.Extra (stripSuffix)


-- | Sorts fields (but not constructors), uses 'Simple' encoding, only works
-- on records.
deriveSafeCopySorted :: Version a -> Name -> Name -> Q [Dec]
deriveSafeCopySorted = internalDeriveSafeCopySorted

{- |
A change from one version of a record (one constructor, several fields) to
another version. We only record the latest version, so we have to be able to
reconstruct the previous version knowing the current version and a list of
'Change's.
-}
data Change
  -- | A field with a particular name and type was removed
  = Removed String (Q Type)
  -- | A field with a particular name and default value was added. We don't
  -- have to record the type since it's already known (remember, we know what
  -- the final version of the record is)
  | Added String Exp

-- | An ADT for versions. Only used in invocations of 'changelog'.
data TypeVersion = Current Int | Past Int
  deriving (Show)

{- |
Generate previous version of the type.

Assume that the new type and the changelog are, respectively:

@
-- version 4
data Foo = FooRec {
  b :: Bool,
  c :: Int }

changelog ''Foo (Current 4, Past 3) [
  Removed "a" [t|String|],
  Added "c" [|if null a then 0 else 1|] ]
@

Then we will generate a type called Foo_v3:

@
data Foo_v3 = FooRec_v3 {
  a_v3 :: String,
  b_v3 :: Bool }
@

We'll also generate a migration instance:

@
instance Migrate Foo where
  type MigrateFrom Foo = Foo_v3
  migrate old = FooRec {
    b = b_v3 old,
    c = if null (a_v3 old) then 0 else 1 }
@

Note that you must use 'deriveSafeCopySorted' for types that use 'changelog'
because otherwise fields will be parsed in the wrong order. Specifically,
imagine that you have created a type with fields “b” and “a” and then removed
“b”. 'changelog' has no way of knowing from “the current version has field
“a”” and “the previous version also had field “b”” that the previous version
had fields “b, a” and not “a, b”. Usual 'deriveSafeCopy' or
'deriveSafeCopySimple' care about field order and thus will treat “b, a” and
“a, b” as different types.
-}
changelog
  :: Name                        -- ^ Type (without version suffix)
  -> (TypeVersion, TypeVersion)  -- ^ New version, old version
  -> [Change]                    -- ^ List of changes between this version
                                 --   and previous one
  -> DecsQ
changelog _ (_newVer, Current _) _ =
  -- We could've just changed the second element of the tuple to be 'Int'
  -- instead of 'TypeVersion' but that would lead to worse-looking changelogs
  fail "changelog: old version can't be 'Current'"
changelog bareTyName (newVer, Past oldVer) changes = do
  -- ------------------------------------------------------------------------
  -- Name and version business
  -- ------------------------------------------------------------------------
  -- First, we can define functions for removing a new-version prefix and for
  -- adding a new/old-version prefix to a bare name. We'll be working with
  -- bare names everywhere.
  let mkBare :: Name -> String
      mkBare n = case newVer of
        Current _ -> nameBase n
        Past v ->
          let suff = ("_v" ++ show v)
          in case stripSuffix suff (nameBase n) of
               Just n' -> n'
               Nothing -> error $
                 printf "changelog: %s doesn't have suffix %s"
                        (show n) (show suff)
  let mkOld, mkNew :: String -> Name
      mkOld n = mkName (n ++ "_v" ++ show oldVer)
      mkNew n = case newVer of
        Current _ -> mkName n
        Past v -> mkName (n ++ "_v" ++ show v)
  -- We know the “base” name (tyName) of the type and we know the
  -- versions. From this we can get actual new/old names:
  let newTyName = mkNew (nameBase bareTyName)
  let oldTyName = mkOld (nameBase bareTyName)
  -- We should also check that the new version exists and that the old one
  -- doesn't.
  whenM (isNothing <$> lookupTypeName (nameBase newTyName)) $
    fail (printf "changelog: %s not found" (show newTyName))
  whenM (isJust <$> lookupTypeName (nameBase oldTyName)) $
    fail (printf "changelog: %s is already present" (show oldTyName))

  -- -----------------------------------------------------------------------
  -- Process the changelog
  -- -----------------------------------------------------------------------
  -- Make separate lists of added and removed fields
  let added :: Map String Exp
      added = M.fromList [(n, e) | Added n e <- changes]
  let removed :: Map String (Q Type)
      removed = M.fromList [(n, t) | Removed n t <- changes]

  -- -----------------------------------------------------------------------
  -- Get information about the new version of the datatype
  -- -----------------------------------------------------------------------
  -- First, 'reify' it. See documentation for 'reify' to understand why we
  -- use 'lookupValueName' here (if we just do @reify newTyName@, we might
  -- get the constructor instead).
  TyConI (DataD _cxt _name _vars _kind cons _deriving) <- do
    mbReallyTyName <- lookupTypeName (nameBase newTyName)
    case mbReallyTyName of
      Just reallyTyName -> reify reallyTyName
      Nothing -> fail $ printf "changelog: type %s not found" (show newTyName)
  -- Do some checks first – we only have to handle simple types for now, but
  -- if/when we need to handle more complex ones, we want to be warned.
  unless (null _cxt) $
    fail "changelog: can't yet work with types with context"
  unless (null _vars) $
    fail "changelog: can't yet work with types with variables"
  unless (isNothing _kind) $
    fail "changelog: can't yet work with types with kinds"
  -- We assume that the type is a single-constructor record.
  con <- case cons of
    [x] -> return x
    []  -> fail "changelog: the type has to have at least one constructor"
    _   -> fail "changelog: the type has to have only one constructor"
  -- Check that the type is actually a record and that there are no strict
  -- fields (which we cannot handle yet); when done, make a list of fields
  -- that is easier to work with. We strip names to their bare form.
  let normalBang = Bang NoSourceUnpackedness NoSourceStrictness
  (recName :: String, fields :: [(String, Type)]) <- case con of
    RecC cn fs
      | all (== normalBang) (fs^..each._2) ->
          return (mkBare cn, [(mkBare n, t) | (n,_,t) <- fs])
      | otherwise -> fail "changelog: can't work with strict/unpacked fields"
    _             -> fail "changelog: the type must be a record"
  -- Check that all 'Added' fields are actually present in the new type
  -- and that all 'Removed' fields aren't there
  for_ (M.keys added) $ \n ->
    unless (n `elem` map fst fields) $ fail $
      printf "changelog: field %s isn't present in %s"
             (show (mkNew n)) (show newTyName)
  for_ (M.keys removed) $ \n ->
    when (n `elem` map fst fields) $ fail $
      printf "changelog: field %s is present in %s \
             \but was supposed to be removed"
             (show (mkNew n)) (show newTyName)

  -- -----------------------------------------------------------------------
  -- Generate the old type
  -- -----------------------------------------------------------------------
  -- Now we can generate the old type based on the new type and the
  -- changelog. First we determine the list of fields (and types) we'll have
  -- by taking 'fields' from the new type, adding 'Removed' fields and
  -- removing 'Added' fields. We still use bare names everywhere.
  let oldFields :: Map String (Q Type)
      oldFields = fmap return (M.fromList fields)
                    `M.union` removed
                    `M.difference` added

  -- Then we construct the record constructor:
  --   FooRec_v3 { a_v3 :: String, b_v3 :: Bool }
  let oldRec = recC (mkOld recName)
                    [varBangType (mkOld fName)
                                 (bangType bangNotStrict fType)
                    | (fName, fType) <- M.toList oldFields]
  -- And the data type:
  --   data Foo_v3 = FooRec_v3 {...}
  let oldTypeDecl = dataD (cxt [])      -- no context
                          oldTyName     -- name of old type
                          []            -- no variables
                          Nothing       -- no explicit kind
                          [oldRec]      -- one constructor
                          (cxt [])      -- not deriving anything

  -- Next we generate the migration instance. It has two inner declarations.
  -- First declaration – “type MigrateFrom Foo = Foo_v3”:
  let migrateFromDecl =
        tySynInstD ''MigrateFrom (tySynEqn [conT newTyName] (conT oldTyName))
  -- Second declaration:
  --   migrate old = FooRec {
  --     b = b_v3 old,
  --     c = if null (a_v3 old) then 0 else 1 }
  migrateArg <- newName "old"
  -- This function replaces accessors in an expression – “a” turns into
  -- “(a_vN old)” if 'a' is one of the fields in the old type
  let replaceAccessors = transform f
        where f (VarE x) | nameBase x `elem` M.keys oldFields =
                AppE (VarE (mkOld (nameBase x))) (VarE migrateArg)
              f x = x
  let migrateDecl = funD 'migrate [
        clause [varP migrateArg]
          (normalB $ recConE (mkNew recName) $ do
             (field, _) <- fields
             let content = case M.lookup field added of
                   -- the field was present in old type
                   Nothing -> appE (varE (mkOld field)) (varE migrateArg)
                   -- wasn't
                   Just e  -> return (replaceAccessors e)
             return $ (mkNew field,) <$> content)
          []
        ]

  let migrateInstanceDecl =
        instanceD
          (cxt [])                        -- no context
          [t|Migrate $(conT newTyName)|]  -- Migrate Foo
          [migrateFromDecl, migrateDecl]  -- associated type & migration func

  -- Return everything
  sequence [oldTypeDecl, migrateInstanceDecl]

-- | Parse a Haskell expression with haskell-src-meta. The difference between
-- @[|exp|]@ and @[hs|exp|]@ is the the former requires all variables in
-- @exp@ to be present in scope at the moment of generation, but the latter
-- doesn't. This makes 'hs' useful for 'changelog'.
hs :: QuasiQuoter
hs = QuasiQuoter {
  quoteExp  = either fail TH.lift . parseExp,
  quotePat  = fail "hs: can't parse patterns",
  quoteType = fail "hs: can't parse types",
  quoteDec  = fail "hs: can't parse declarations" }

-- | A type for specifying what constructors existed in an old version of a
-- sum datatype.
data GenConstructor
  = Copy Name                         -- ^ Just reuse the constructor
                                      --   existing now.
  | Custom String [(String, Q Type)]  -- ^ The previous version had a
                                      --   constructor with such-and-such
                                      --   name and such-and-such fields.

-- | Generate an old version of a sum type (used for 'SafeCopy').
genVer
  :: Name                  -- ^ Name of type to generate old version for
  -> Int                   -- ^ Version to generate
  -> [GenConstructor]      -- ^ List of constructors in the version we're
                           --   generating
  -> Q [Dec]
genVer tyName ver constructors = do
  -- Get information about the new version of the datatype
  TyConI (DataD _cxt _name _vars _kind cons _deriving) <- reify tyName
  -- Let's do some checks first
  unless (null _cxt) $
    fail "genVer: can't yet work with types with context"
  unless (null _vars) $
    fail "genVer: can't yet work with types with variables"
  unless (isNothing _kind) $
    fail "genVer: can't yet work with types with kinds"

  let oldName n = mkName (nameBase n ++ "_v" ++ show ver)

  let copyConstructor conName =
        case [c | c@(RecC n _) <- cons, n == conName] of
          [] -> fail ("genVer: couldn't find a record constructor " ++
                      show conName)
          [RecC _ fields] ->
            recC (oldName conName)
                 (map return (fields & each._1 %~ oldName))
          other -> fail ("genVer: copyConstructor: got " ++ show other)

  let customConstructor conName fields =
        recC (oldName (mkName conName))
             [varBangType (oldName (mkName fName))
                          (bangType bangNotStrict fType)
               | (fName, fType) <- fields]

  cons' <- for constructors $ \genCons ->
    case genCons of
      Copy conName -> copyConstructor conName
      Custom conName fields -> customConstructor conName fields

  decl <- dataD
    -- no context
    (cxt [])
    -- name of our type (e.g. SomeType_v3 if the previous version was 3)
    (oldName tyName)
    -- no variables
    []
    -- no explicit kind
    Nothing
    -- constructors
    (map return cons')
    -- not deriving anything
    (cxt [])
  return [decl]

-- | A type for migrating constructors from an old version of a sum datatype.
data MigrateConstructor
  = CopyM Name             -- ^ Copy constructor without changes
  | CustomM String ExpQ    -- ^ The old constructor with such-and-such name
                           --   should be turned into a value of the new type
                           --   (i.e. type of current version) using
                           --   such-and-such code.

-- | Generate 'SafeCopy' migration code for a sum datatype.
migrateVer
  :: Name                  -- ^ Type we're migrating to
  -> Int                   -- ^ Version we're migrating from
  -> [MigrateConstructor]  -- ^ For each constructor existing in the (old
                           --   version of) type, a specification of how to
                           --   migrate it.
  -> Q Exp
migrateVer tyName ver constructors = do
  -- Get information about the new version of the datatype
  TyConI (DataD _cxt _name _vars _kind cons _deriving) <- reify tyName
  -- Let's do some checks first
  unless (null _cxt) $
    fail "migrateVer: can't yet work with types with context"
  unless (null _vars) $
    fail "migrateVer: can't yet work with types with variables"
  unless (isNothing _kind) $
    fail "migrateVer: can't yet work with types with kinds"

  let oldName n = mkName (nameBase n ++ "_v" ++ show ver)

  arg <- newName "x"

  let copyConstructor conName =
        case [c | c@(RecC n _) <- cons, n == conName] of
          [] -> fail ("migrateVer: couldn't find a record constructor " ++
                      show conName)
          [RecC _ fields] -> do
            -- SomeConstr_v3{} -> SomeConstr (field1 x) (field2 x) ...
            let getField f = varE (oldName (f ^. _1)) `appE` varE arg
            match (recP (oldName conName) [])
                  (normalB (appsE (conE conName : map getField fields)))
                  []
          other -> fail ("migrateVer: copyConstructor: got " ++ show other)

  let customConstructor conName res =
        match (recP (oldName (mkName conName)) [])
              (normalB (res `appE` varE arg))
              []

  branches' <- for constructors $ \genCons ->
    case genCons of
      CopyM conName -> copyConstructor conName
      CustomM conName res -> customConstructor conName res

  lam1E (varP arg) (caseE (varE arg) (map return branches'))

----------------------------------------------------------------------------
-- Internal stuff
----------------------------------------------------------------------------

internalDeriveSafeCopySorted :: Version a -> Name -> Name -> Q [Dec]
internalDeriveSafeCopySorted versionId kindName tyName = do
  info <- reify tyName
  internalDeriveSafeCopySorted' versionId kindName tyName info

-- This code was mostly copied from safecopy.
internalDeriveSafeCopySorted' :: Version a -> Name -> Name -> Info -> Q [Dec]
internalDeriveSafeCopySorted' versionId kindName tyName info =
  case info of
#if MIN_VERSION_template_haskell(2,11,0)
    TyConI (DataD context _name tyvars _kind cons _derivs)
#else
    TyConI (DataD context _name tyvars cons _derivs)
#endif
      | length cons > 255 -> fail $ "Can't derive SafeCopy instance for: " ++ show tyName ++
                                    ". The datatype must have less than 256 constructors."
      | otherwise         -> worker context tyvars (zip [0..] cons)

#if MIN_VERSION_template_haskell(2,11,0)
    TyConI (NewtypeD context _name tyvars _kind con _derivs) ->
#else
    TyConI (NewtypeD context _name tyvars con _derivs) ->
#endif
      worker context tyvars [(0, con)]

    FamilyI _ insts -> do
      decs <- forM insts $ \inst ->
        case inst of
#if MIN_VERSION_template_haskell(2,11,0)
          DataInstD context _name ty _kind cons _derivs ->
#else
          DataInstD context _name ty cons _derivs ->
#endif
              worker' (foldl appT (conT tyName) (map return ty)) context [] (zip [0..] cons)

#if MIN_VERSION_template_haskell(2,11,0)
          NewtypeInstD context _name ty _kind con _derivs ->
#else
          NewtypeInstD context _name ty con _derivs ->
#endif
              worker' (foldl appT (conT tyName) (map return ty)) context [] [(0, con)]
          _ -> fail $ "Can't derive SafeCopy instance for: " ++ show (tyName, inst)
      return $ concat decs
    _ -> fail $ "Can't derive SafeCopy instance for: " ++ show (tyName, info)
  where
    worker = worker' (conT tyName)
    worker' tyBase context tyvars cons =
      let ty = foldl appT tyBase [ varT $ S.tyVarName var | var <- tyvars ]
#if MIN_VERSION_template_haskell(2,10,0)
          safeCopyClass args = foldl appT (conT ''SafeCopy) args
#else
          safeCopyClass args = classP ''SafeCopy args
#endif
      in (:[]) <$> instanceD (cxt $ [safeCopyClass [varT $ S.tyVarName var] | var <- tyvars] ++ map return context)
                                       (conT ''SafeCopy `appT` ty)
                                       [ mkPutCopySorted cons
                                       , mkGetCopySorted (show tyName) cons
                                       , valD (varP 'version) (normalB $ litE $ integerL $ fromIntegral $ S.unVersion versionId) []
                                       , valD (varP 'kind) (normalB (varE kindName)) []
                                       , funD 'errorTypeName [clause [wildP] (normalB $ litE $ StringL (show tyName)) []]
                                       ]

mkPutCopySorted :: [(Integer, Con)] -> DecQ
mkPutCopySorted cons =
    funD 'putCopy (map mkPutClause cons)
  where
    manyConstructors = length cons > 1
    mkPutClause (conNumber, RecC recName (sortFields -> fields)) = do
      arg <- newName "arg"
      let putConNumber = [|putWord8 $(lift conNumber)|]
          putField (field, _, _) = [|safePut ($(varE field) $(varE arg))|]
          putCopyBody = varE 'contain `appE` doE (
                          [ noBindS putConNumber | manyConstructors ] ++
                          [ noBindS (putField f) | f <- fields ] )
      clause [asP arg (recP recName [])] (normalB putCopyBody) []
    mkPutClause (_, con) =
      fail ("Only record constructors are supported: " ++ show (S.conName con))

mkGetCopySorted :: String -> [(Integer, Con)] -> DecQ
mkGetCopySorted tyName cons =
    valD (varP 'getCopy) (normalB [|contain $mkLabel|]) []
  where
    mkLabel = [|label $(lift labelString) $getCopyBody|]
    labelString = tyName ++ ":"
    getCopyBody = case cons of
      [(_, con)] -> mkGetBody con
      _ -> do
        tagVar <- newName "tag"
        let conMatch (i, con) =
              match (litP $ IntegerL i) (normalB $ mkGetBody con) []
        let noConMatch =
              match wildP (normalB [|fail $(errorMsg tagVar)|]) []
        doE [ bindS (varP tagVar) [|getWord8|]
            , noBindS $ caseE (varE tagVar)
                              (map conMatch cons ++ [noConMatch]) ]
    mkGetBody (RecC recName (sortFields -> fields)) = do
      fieldVars <- mapM newName [nameBase f | (f, _, _) <- fields]
      let getField fieldVar = bindS (varP fieldVar) [|safeGet|]
      let makeRecord = recConE recName
            [(f,) <$> varE v | ((f, _, _), v) <- zip fields fieldVars]
      doE ([ getField v | v <- fieldVars ] ++
           [ noBindS [|return $makeRecord|] ])
    mkGetBody con =
      fail ("Only record constructors are supported: " ++ show (S.conName con))
    errorMsg tagVar = [|$(lift s1) ++ show $(varE tagVar) ++ $(lift s2)|]
      where
        s1, s2 :: String
        s1 = "Could not identify tag \""
        s2 = concat [ "\" for type "
                    , show tyName
                    , " that has only "
                    , show (length cons)
                    , " constructors. Maybe your data is corrupted?" ]

sortFields :: [VarStrictType] -> [VarStrictType]
-- We sort by length and then lexicographically, so that relative ordering
-- would be preserved when version suffix is added – otherwise these fields
-- would be sorted in different order after adding a suffix:
--
-- foo         fooBar_v3
-- fooBar      foo_v3
sortFields = sortOn (\(n, _, _) -> (length (nameBase n), nameBase n))

----------------------------------------------------------------------------
-- Utilities
----------------------------------------------------------------------------

bangNotStrict :: Q Bang
bangNotStrict = bang noSourceUnpackedness noSourceStrictness
