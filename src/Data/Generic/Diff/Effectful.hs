{-#  LANGUAGE GADTs  #-}
{-#  LANGUAGE TypeFamilies  #-}
{-#  LANGUAGE TypeOperators  #-}
{-#  LANGUAGE MultiParamTypeClasses  #-}
{-#  LANGUAGE FlexibleInstances  #-}
{-#  LANGUAGE ViewPatterns, FlexibleContexts, ImpredicativeTypes, StandaloneDeriving, DeriveFunctor, UndecidableInstances, PolyKinds, ScopedTypeVariables  #-}

{-#  OPTIONS_GHC -Wall -fno-warn-name-shadowing  #-}

module Data.Generic.Diff.Effectful ( diffM, patchM, Ize(..), pmash, smash) where

import Data.Generic.Diff
import System.IO.Unsafe
import Control.Applicative
import Control.Monad
import Unsafe.Coerce ( unsafeCoerce )

data BFam :: (* -> *) -> * -> * -> * where
  False' :: BFam p Bool Nil
  True' :: BFam p Bool Nil
  Just' :: BFam p a ts -> BFam p (Maybe a) ts
  Pair :: (List (BFam p) as, List (BFam p) bs) => BFam p a as -> BFam p b bs -> BFam p (a, b) (as `Append` bs)
  ListNil :: List (BFam p) as => BFam p a as -> BFam p [a] Nil
  ListCons :: List (BFam p) as => BFam p a as -> BFam p [a] (a `Cons` [a] `Cons` Nil)
  ListCons' :: List (BFam p) as => BFam p a as -> BFam p [a] ([a] `Cons` as) -- non-move
  IZE :: List (BFam p) ts => BFam p t ts -> BFam p (p t) (Map p ts)

instance Type (BFam p) a => Type (BFam p) [a] where
  --constructors = Concr ListNil : [iFeelDirty Concr (IsCons $ isList cc) (ListCons' cc) | Concr cc <- constructors]  -- non-move
  constructors = head [Concr (ListNil cc) | Concr cc <- constructors] : [head [Concr (ListCons cc) | Concr cc <- constructors]]

instance Ize BFam m => Family (BFam m) where
  False' `decEq` False' = Just (Refl, Refl)
  True' `decEq` True' = Just (Refl, Refl)
  Just' l `decEq` Just' r = do (Refl, Refl) <- l `decEq` r; return (Refl, Refl)
  Pair l l' `decEq` Pair r r' = do (Refl, Refl) <- l `decEq` r; (Refl, Refl) <- l' `decEq` r'; return (Refl, Refl)
  ListNil l `decEq` ListNil r = do (Refl, Refl) <- l `decEq` r; return (Refl, Refl)
  ListCons l `decEq` ListCons r = do (Refl, Refl) <- l `decEq` r; return (Refl, Refl)
  IZE l `decEq` IZE r = do (Refl, Refl) <- l `decEq` r; return (Refl, Refl)
  _ `decEq` _ = Nothing

  fields False' False = Just CNil
  fields True' True = Just CNil
  fields (ListNil _) [] = Just CNil
  --fields (ListCons' _) (a:as) = do fs <- fields d a; return $ as `CCons` fs  -- non-move
  fields (ListCons _) (a:as) = return $ a `CCons` as `CCons` CNil
  fields (Just' d) (Just t) = fields d t
  fields (Pair a b) (as, bs) = liftM2 (isList a `append` isList b) (fields a as) (fields b bs)
  fields (IZE d) (extract d -> v) = fmap (lift d) (fields d v)
  fields _ _ = Nothing

  apply False' CNil = False
  apply True' CNil = True
  apply (ListNil _) CNil = []
  apply (ListCons _) (a `CCons` as `CCons` CNil) = a : as
  apply (Just' d) ts = Just $ apply d ts
  apply (Pair a b) ts = (apply a as, apply b bs)
      where (as, bs) = split (isList a) ts
  apply (IZE d) ins = ize d ins

  string False' = "False"
  string True' = "True"
  string (Just' d) = "(Just " ++ string d ++ ")"
  string (ListNil _) = "[]"
  string (ListCons _) = "(:)"
  string (Pair a b) = "(" ++ string a ++ ", " ++ string b ++ ")"
  string (IZE i) = '!' : string i

newtype E m t = E (Either t (m t))

instance Functor m => Functor (E m) where
  fmap f (E (Left t)) = E . Left $ f t
  fmap f (E (Right m)) = E . Right $ fmap f m

instance (Functor (E m), Monad (E m)) => Applicative (E m) where
  pure = return
  (<*>) = ap

instance Monad (E IO) where
  return = E . Left
  E (Left a) >>= f = f a
  E (Right io) >>= f = unsafePerformIO $ io >>= return . f


class (Monad m, Family (f m)) => Ize f m where
  extract :: f m t ts -> m t -> t
  ize :: List (f m) ts => f m t ts -> Map m ts -> m t
  -- | When the node matches, but the subtrees not necessarily,
  -- then permit the user to optimize
  copy :: List (f m) ts => f m t ts -> ts -> t
  copy = apply
  upgradeIsList :: IsList (f m) ts -> IsList (f m) (Map m ts)

instance Ize BFam IO where
  extract = const unsafePerformIO
  ize True' CNil = putStrLn "Licht EIN" >> return True
  ize False' CNil = putStrLn "Licht AUS" >> return False
  ize (a `Pair` b) ts = return (,) `ap` ize a as `ap` ize b bs
      where (as, bs) = split (isList a) (unsafeCoerce ts) -- NEED ASSURANCE
            split :: IsList f txs -> Append (Map IO txs) tys -> (Map IO txs, tys)
            split IsNil         ys              = (CNil, ys)
            split (IsCons isxs) (CCons x xsys)  =  let  (xs, ys) = split isxs xsys
                                                   in   (CCons x xs, ys)
            --law :: IsList (BFam IO) (Append (Map IO as) (Map IO bs)) -> IsList (BFam IO) (Map IO (as `Append` bs))
            --law = unsafeCoerce
  upgradeIsList IsNil = IsNil
  --upgradeIsList (IsCons r) = IsCons (upgradeIsList r)

liftE :: m t -> E m t
liftE = E . Right

instance Ize BFam (E IO) where
  extract _ (E (Left a)) = a
  copy (IZE True') _ = return True -- $ apply True' parts -- DOABLE: Map must be injective to make this work!
  --copy (IZE True') parts = return $ copy True' parts -- DOABLE: Map must be injective to make this work!
  copy (IZE False') _ = return False
  copy (IZE what) parts = error $ "what to do with " -- ++ show heh ++ " parts: " ++ show parts
  --ize True' CNil = liftE (putStrLn "Licht EIN") >> (return $ apply True' CNil) -- DOABLE: Map must be injective to make this work!
  ize True' CNil = liftE (putStrLn "Licht EIN") >> copy (IZE True') CNil -- WORKS
  --ize True' CNil = liftE (putStrLn "Licht EIN") >> return True
  ize False' CNil = liftE (putStrLn "Licht AUS") >> return False
  ize (a `Pair` b) ts = return (,) `ap` ize a as `ap` ize b bs
      where (as, bs) = split (isList a) (unsafeCoerce ts) -- NEED ASSURANCE
            split :: IsList f txs -> Append (Map (E IO) txs) tys -> (Map (E IO) txs, tys)
            split IsNil         ys              = (CNil, ys)
            split (IsCons isxs) (CCons x xsys)  =  let  (xs, ys) = split isxs xsys
                                                   in   (CCons x xs, ys)
  upgradeIsList IsNil = IsNil
  --upgradeIsList (IsCons r) = IsCons (upgradeIsList r)

instance Ize BFam p => Type (BFam p) Bool where
  constructors = [Concr False', Concr True']

instance (Type (BFam p) a, Type (BFam p) b) => Type (BFam p) (a, b) where
  constructors = [concrPair cca ccb (appendDict (isList cca) (listDict ccb)) | Concr cca <- constructors, Concr ccb <- constructors]
  -- ###constructors = [iFeelDirty Concr (isList cca `appendList` isList ccb) (cca `Pair` ccb) | Concr cca <- constructors, Concr ccb <- constructors]
  -- ###            ++ [iFeelDirty' Abstr (isList (cca undefined) `appendList` isList (ccb undefined)) (\(a, b) -> cca a `Pair` ccb b) | Abstr cca <- constructors, Abstr ccb <- constructors]

concrPair :: (List (BFam p) ts, List (BFam p) ts') => BFam p a ts -> BFam p b ts' -> Dict (List (BFam p)) (ts `Append` ts') -> Con (BFam p) (a, b)
concrPair cca ccb Dict = Concr (cca `Pair` ccb)

listDict :: List fam ts => fam t ts -> Dict (List fam) ts
listDict _ = Dict

appendDict :: IsList fam ts -> Dict (List fam) ts' -> Dict (List fam) (ts `Append` ts')
appendDict IsNil Dict = Dict
appendDict (IsCons r) dl = case appendDict r dl of
                             Dict -> Dict


{-
iFeelDirty :: (forall ts . List f ts => f t ts -> Con f t) -> (forall ts . IsList f ts -> f t ts -> Con f t)
iFeelDirty = unsafeCoerce

iFeelDirty' :: Eq t => (forall ts . List f ts => (t -> f t ts) -> Con f t) -> (forall ts . IsList f ts -> (t -> f t ts) -> Con f t)
iFeelDirty' = unsafeCoerce

iFeelDirtier :: (forall ts . List f (Map p ts) => f t ts -> f (p t) (Map p ts) -> Con f (p t)) -> (forall ts . IsList f (Map p ts) -> f t ts -> f (p t) (Map p ts) -> Con f (p t))
iFeelDirtier = unsafeCoerce

iFeelDirtier' :: Eq t => (forall ts . List f (Map p ts) => (t -> f t ts) -> (p t -> f (p t) (Map p ts)) -> Con f (p t)) -> (forall ts . IsList f (Map p ts) -> (t -> f t ts) -> (p t -> f (p t) (Map p ts)) -> Con f (p t))
iFeelDirtier' = unsafeCoerce
-}

instance Show a => Show (E IO a) where
  show (E (Left a)) = show a
  show (E (Right _)) = "<an action>"

--instance (Ize BFam p, Type (BFam p) a) => Type (BFam p) (p a) where
  -- ###constructors = [iFeelDirtier (const Concr) (upgradeIsList (isList cc)) cc (IZE cc) | Concr cc <- constructors]
--instance (Ize fam p, Type (fam p) a) => Type (fam p) (p a) where
--  constructors = [iFeelDirtier (const Concr) (upgradeIsList (isList cc)) cc (IZE cc) | Concr cc <- constructors]

lift f = go f list
    where go :: Monad p => BFam p t ts -> IsList (BFam p) ts -> ts -> Map p ts
          go _ IsNil CNil = CNil
          go f (IsCons r) (CCons h t) = CCons (return h) (go (cut f) r t)
          cut :: BFam p t (Cons t' ts) -> BFam p t ts
          cut = undefined

pmash :: forall fam ts m f t . (Family fam, List fam ts) => m (f t) -> (forall a b . m a -> m b -> m b) -> fam (f t) ts -> Map m ts -> m (f t)
pmash base par fam ms = go (isList fam) ms
    where go :: IsList fam ts' -> Map m ts' -> m (f t)
          go IsNil CNil = base
          go (IsCons rest) (m `CCons` ms) = m `par` go rest ms

-- implement smash in terms of pmash (kindof)
smash' :: (Family fam, List fam ts, Monad m) => fam (f t) ts -> Map m ts -> m (f t)
smash' = pmash (return undefined) (>>)

smash :: (Family fam, List fam ts, Monad m) => fam (f t) ts -> Map m ts -> m (f t)
smash fam ms = go (isList fam) ms
    where go :: Monad m => IsList fam ts -> Map m ts -> m (f t)
          go IsNil CNil = return undefined
          go (IsCons rest) (m `CCons` ms) = m >> go rest ms

-- diffIO: superseded by diffM!!
diffIO :: Type (BFam IO) (IO t) => IO t -> IO t -> EditScript (BFam IO) (IO t) (IO t)
diffIO = diff

diffM :: Type (fam p) (p t) => p t -> p t -> EditScript (fam p) (p t) (p t)
diffM = diff

diffP :: (Type (BFam IO) a, Type (BFam IO) b) => (a, b) -> (a, b) -> EditScript (BFam IO) (a, b) (a, b)
diffP = diff


-- | Apply the edit script to a value.
patchM :: Ize f m => EditScript (f m) x y -> x -> y
patchM d x = case patchLM d (CCons x CNil) of
                CCons y CNil -> y

-- | Underlying implementation of 'patch', works with (heterogeneous) lists of
-- values, potentially building monadic actions along the way.
patchLM :: forall f m txs tys . Ize f m => EditScriptL (f m) txs tys -> txs -> tys -- (Map m tys)
patchLM (Ins  c   d) = insert apply c .  patchLM d
patchLM (Del  c   d) =                   patchLM d . delete c
patchLM (Cpy  c   d) = insert copy  c .  patchLM d . delete c
patchLM (CpyTree  d) = \(CCons x xs) -> CCons x . patchLM d $ xs
patchLM End          = \CNil -> CNil

insert :: (Type f t, List f ts, List f txs) => (f t ts -> ts -> t) -> f t ts -> Append ts txs -> Cons t txs
insert app c xs = CCons (app c txs) tys
  where (txs, tys) = split (isList c) xs

delete :: (Type f t, List f ts, List f txs) => f t ts -> Cons t txs -> Append ts txs
delete c (CCons x xs) =
  case fields c x of
    Nothing  -> error "Patching failed"
    Just ts  -> append (isList c) list ts xs
