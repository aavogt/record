{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}
module Record.Append (Append(..)) where
import BasePrelude 
import Record.Types
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Record.Types
import GHC.Exts (Constraint)
import GHC.TypeLits (Symbol)

import Data.HList.CommonMain
import Data.HList.HSort
import Data.List (sort)
import Record.Lens (view, Lens)


{- |

The instances look like:

@
instance 
  ( -- sort the input types (type level) which have been
    -- labeled with which side they come from
    HSort [Tagged n (FromN a), Tagged m (FromM a)]
          [Tagged i (fromI x), Tagged j (fromJ y)],

    -- now the constraints that actually supply the lookup
    -- that makes the new record:
    ViewFrom fromI i (Record1 n a) (Record1 m b) x,
    ViewFrom fromJ j (Record1 n a) (Record1 m b) y)

    => Append (Record1 n a) (Record1 m b) (Record2 i x j y) where

  append nr mr =
    Record2
       (viewFrom (Proxy :: Proxy fromI)
                 (undefined :: FieldName i)
                 nr
                 mr)

       (viewFrom (Proxy :: Proxy fromJ)
                 (undefined :: FieldName j)
                 nr
                 mr)
@

which go up to Record24

-}
class Append a b ab where
    append :: a -> b -> ab


-- could be data From a = FromM a | FromN a,
-- but that 
data FromM a
data FromN a

-- | `a` comes from `nr` or `mr` but we don't know
-- until looking at the from
class ViewFrom (from :: * -> *) s nr mr a where
    viewFrom :: Proxy from -> FieldName s -> nr -> mr -> a

instance Field' s mr a => ViewFrom FromM s nr mr a where
    -- Record.Lens.view should be
    -- view :: Lens s s a a -> s a
    -- that avoids the ambiguity that needs an annotation here
    viewFrom _ s n m = view (fieldLens s :: Lens mr mr a a) m

instance Field' s nr a => ViewFrom FromN s nr mr a where
    viewFrom _ s n m = view (fieldLens s :: Lens nr nr a a) n


let f n m = do
      let recNT n = case ''Record1 of
                 Name _ ng -> Name (OccName ("Record"++show n)) ng

          recN n = case 'Record1 of
                     Name _ ng -> Name (OccName ("Record"++show n)) ng

      ns <- replicateM n (newName "n")
      ms <- replicateM m (newName "m")

      nes <- replicateM n (newName "ne")
      mes <- replicateM m (newName "me")

      nms <- replicateM (n+m) (newName "nm")
      nmes <- replicateM (n+m) (newName "mme")
      nmesF <- replicateM (n+m) (newName "from")

      let appendNM = [| \ nr mr ->
                      $(foldl (\ r (f, nm, e) ->
                                  [| $r (viewFrom
                                              (Proxy :: $(conT ''Proxy) $(varT f))
                                              (undefined :: FieldName $(varT nm))
                                              nr
                                              mr :: $(varT e)) |])
                              (conE (recN (n+m)))
                              (zip3 nmesF nms nmes)
                        ) |]

      let mkApplied n ns nes = foldl (\ f (n,ne) -> [t| $f $(varT n) $(varT ne) |]) 
                                  (conT (recNT n))
                                  (ns `zip` nes)
          
          nTy,mTy,nmTy :: TypeQ
          nTy = mkApplied n ns nes
          mTy = mkApplied m ms mes
          nmTy = mkApplied (n+m) nms nmes

          toTaggedList :: [(Name,TypeQ)] -> TypeQ
          toTaggedList = foldr (\ (t,e) xs -> [t| Tagged $(varT t) $e ': $xs |])  [t| '[] |]

          tnm1 :: TypeQ
          tnm1 = toTaggedList
                    (zip (ns ++ ms)
                         ((map (\e -> [t| FromN $(varT e) |]) nes) ++
                          (map (\e -> [t| FromM $(varT e) |]) mes)))

          tnm2 :: TypeQ
          tnm2 = toTaggedList (nms `zip`
                                (zipWith (\ f e -> [t| $(varT f) $(varT e) |]) nmesF nmes))

          viewFromCxts :: [Q Pred] 
          viewFromCxts = [ classP ''ViewFrom [varT f, varT s, nTy, mTy, varT e]
                                       | (f,s,e) <- zip3 nmesF nms nmes ]

          toL :: [Name] -> TypeQ
          toL = foldr (\ x xs -> [t| $(varT x) ': $xs |]) [t| '[] |]

      z <- newName "z"
      fmap (:[]) $ instanceD (sequence $ [ classP ''HSort [tnm1, tnm2],
                              varT z `equalP` nmTy]
                            ++ viewFromCxts)
              [t| Append $nTy $mTy $(varT z) |]
              [valD (varP 'append) (normalB appendNM) []]

{-    alternative, which does not work (with ghc-7.8) because there
      does not seem to be a way to collapse viewFromCxts :: [Q Pred]
      into Q Pred (a separate type family F nmesF nms nTy mTy nmes :: Constraint
      lists cannot be spliced)
      [d| instance (HSort ok $tnm1 $tnm2, z ~ $nmTy, $viewFromCxt) =>
                   Append $nTy $mTy z where
                  append = $appendNM |]
      -}

 in concat `fmap` sequence [ f n m | n <- [1 .. 24], m <- [1 .. 24], n+m <= 24 ]


#ifdef TESTING
a <+> b = append a b

infixr <+>


type T0 = [r| { w :: () } |]
type T1 = [r| { x :: Int } |]
type T2 = [r| { y :: Char } |]
type T3 = [r| { z :: Double } |]

{- | all permutations of t0 <+> t1 <+> t2 <+> t3 
give the same type.

>>> :t _1
_1 :: Record4 "w" () "x" Int "y" Char "z" Double

>>> :t _23
_23 :: Record4 "w" () "x" Int "y" Char "z" Double

-}
t0 = [r| { w = () } |] :: T0
t1 = [r| { x = 1 } |] :: T1
t2 = [r| { y = 'x' } |] :: T2
t3 = [r| { z = 2.4 } |] :: T3

let ns = map varE ['t0 , 't1, 't2 , 't3]

 in fmap concat $ sequence
           $ map (\(i, e) -> [d| $(varP (mkName ("_"++show i))) = $e |]) 
          $ zip [1 .. ]
          $ map (foldr1 (\a b -> [| $a <+> $b |])) (permutations ns) 
#endif
