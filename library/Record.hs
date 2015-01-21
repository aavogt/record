module Record
(
  record,
  lens,
  -- ** Shorthands
  r,
  l,
)
where

import BasePrelude
import Language.Haskell.TH
import Language.Haskell.TH.Quote
import qualified Record.Lens as Lens
import qualified Record.Parser as Parser
import qualified Data.Text as T

import Data.HList.CommonMain

-- | A shorthand alias to 'record'.
r :: QuasiQuoter
r = record

-- | A shorthand alias to 'lens'.
l :: QuasiQuoter
l = lens

-- |
-- A quasiquoter, which generates record expressions and types,
-- depending on the context it's used in.
--
-- Here is how you can use it to declare types:
--
-- >type Person =
-- >  [record| {name :: String, birthday :: {year :: Int, month :: Int, day :: Int}} |]
--
-- To declare functions:
--
-- >getAge :: [record| {name :: String, age :: Int} |] -> Int
--
-- To declare values:
--
-- >person :: Person
-- >person =
-- >  [record| {name = "Grigori Yakovlevich Perelman",
-- >            birthday = {year = 1966, month = 6, day = 13}} |]
--
record :: QuasiQuoter
record =
  QuasiQuoter
    (exp)
    (const $ fail "Pattern context is not supported")
    (type')
    (const $ fail "Declaration context is not supported")
  where
    exp =
      renderExp <=<
      either (fail . showString "Parser failure: ") return .
      Parser.run (Parser.qq Parser.exp) . fromString
    type' =
      renderType <=<
      either (fail . showString "Parser failure: ") return .
      Parser.run (Parser.qq Parser.type') . fromString

-- |
-- A quasiquoter, which generates a 'Lens.Lens'.
-- Lens is your interface to accessing and modifying the fields of a record.
--
-- Here is how you can use it:
--
-- >getPersonBirthdayYear :: Person -> Int
-- >getPersonBirthdayYear =
-- >  Record.Lens.view ([lens|birthday|] . [lens|year|])
--
-- For your convenience you can compose lenses from inside of the quotation:
--
-- >setPersonBirthdayYear :: Int -> Person -> Person
-- >setPersonBirthdayYear =
-- >  Record.Lens.set [lens|birthday.year|]
--
-- You can also use this function to manipulate tuples of arity up to 24:
--
-- >mapThirdElement :: (Char -> Char) -> (Int, String, Char) -> (Int, String, Char)
-- >mapThirdElement =
-- >  Record.Lens.over [lens|3|]
lens :: QuasiQuoter
lens =
  QuasiQuoter
    (exp)
    (const $ fail "Pattern context is not supported")
    (const $ fail "Type context is not supported")
    (const $ fail "Declaration context is not supported")
  where
    exp =
      either (fail . showString "Parser failure: ") renderLens .
      Parser.run (Parser.qq Parser.lens) . fromString

renderLens :: Parser.Lens -> ExpQ
renderLens =
  foldl1 composition .
  fmap renderSingleLens
  where
    composition a b = [| $a . $b |]

renderSingleLens :: T.Text -> ExpQ
renderSingleLens s = [| hLens' (Label :: Label $(textLitT s)) |]

renderRecordType :: Parser.RecordType -> TypeQ
renderRecordType l = do
  checkDuplicateLabels l
  [t| Record $(makeHListTy l) |]

makeHListTy :: [(T.Text, Parser.Type)] -> TypeQ
makeHListTy =
  foldr (\ (l,t) xs -> [t| Tagged $(textLitT l) $(renderType t) ': $xs |])
         [t| '[] |]

renderRecordExp :: [(T.Text, Parser.Exp)] -> ExpQ
renderRecordExp l = do
    checkDuplicateLabels l
    [| Record $(makeHListExp l) |]

checkDuplicateLabels :: (Show l, Ord l) => [(l,a)] -> Q ()
checkDuplicateLabels l =
  maybe (return ()) (fail . showString "Duplicate labels: " . show) $
  mfilter (not . null) . Just $
  map (fst . head) $
  filter ((> 1) . length) $
  groupWith fst l

textLitT :: T.Text -> TypeQ
textLitT =
  litT . strTyLit . T.unpack

makeHListExp :: [(T.Text, Parser.Exp)] -> ExpQ
makeHListExp =
    foldr ( \ (l, v) xs -> [| ((Label :: Label $(textLitT l))
                                  .=. $(renderExp v)) `HCons` $xs |]
            )
          [| HNil |]
     . sortWith fst


renderType :: Parser.Type -> TypeQ
renderType =
  \case
    Parser.Type_App a b  -> [t| $(renderType a) $(renderType b) |]
    Parser.Type_Var n    -> varT (mkName (T.unpack n))
    Parser.Type_Con n    -> conT (mkName (T.unpack n))
    Parser.Type_Tuple a  -> tupleT a
    Parser.Type_Arrow    -> arrowT
    Parser.Type_List     -> listT
    Parser.Type_Record a -> renderRecordType a

renderExp :: Parser.Exp -> ExpQ
renderExp =
  \case
    Parser.Exp_Record r   -> renderRecordExp r
    Parser.Exp_Var n      -> dyn (T.unpack n)
    Parser.Exp_Con n      -> conE (mkName (T.unpack n))
    Parser.Exp_TupleCon a -> conE (tupleDataName a)
    Parser.Exp_Nil        -> [| [] |]
    Parser.Exp_Lit l      -> litE (renderLit l)
    Parser.Exp_App a b    -> [| $(renderExp a) $(renderExp b) |]
    Parser.Exp_List l     -> listE (renderExp <$> l)
    Parser.Exp_Sig e t    -> sigE (renderExp e) (renderType t)

renderLit :: Parser.Lit -> Lit
renderLit =
  \case
    Parser.Lit_Char c -> CharL c
    Parser.Lit_String t -> StringL (T.unpack t)
    Parser.Lit_Integer i -> IntegerL i
    Parser.Lit_Rational r -> RationalL r

