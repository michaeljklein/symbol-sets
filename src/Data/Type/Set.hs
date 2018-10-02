-- {-# LANGUAGE DeriveDataTypeable #-}
-- {-# LANGUAGE FlexibleContexts #-}
-- {-# LANGUAGE GADTs #-}
-- {-# LANGUAGE KindSignatures #-}
-- {-# LANGUAGE TupleSections #-}
-- {-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Type.Set where

import Control.DeepSeq (NFData(..))
import Control.Monad (liftM2)
import Data.Constraint ((:-)(..), Dict(..), unmapDict, withDict)
import Data.Kind
import Data.Proxy (Proxy(..))
import Data.Reflection (Reifies(..))
import GHC.Exts (Constraint)

-- | The constraint that all of the elements of the given list satisfy the given constraint.
type family AllElemsC (c :: k -> Constraint) (as :: [k]) :: Constraint where
  AllElemsC _ '[] = ()
  AllElemsC c (x ': xs) = (c x, AllElemsC c xs)

-- | A newtype-wrapped dictionary of the constraint `AllElemsC`
newtype AllElems (c :: k -> Constraint) (as :: [k]) = AllElems
  { allElemsDict :: Dict (AllElemsC c as)
  } deriving (Eq, Ord, NFData)

-- | Construct an instance of `AllElems`
allElems :: AllElemsC c as => AllElems c as
allElems = AllElems Dict

-- | `AllElems` is vacuously true for any `Constraint` on the empty list
emptyAllElems :: forall (c :: k -> Constraint). AllElems c '[]
emptyAllElems = allElems

-- | If @`AllElems` c (a ': as)`@ then @c a@
headAllElems :: AllElems c (a ': as) -> Dict (c a)
headAllElems AllElems{..} = allElemsDict `withDict` Dict

-- | If @`AllElems` c (a ': as)`@ then @`AllElems` c as@
tailAllElems :: AllElems c (a ': as) -> AllElems c as
tailAllElems AllElems{..} = allElemsDict `withDict` allElems

-- | `headAllElems` and `tailAllElems`
unconsAllElems :: AllElems c (a ': as) -> (Dict (c a), AllElems c as)
unconsAllElems = liftM2 (,) headAllElems tailAllElems

-- | Concatenate an instance of a `Constraint` onto the front of an `AllElems`
consAllElems :: Dict (c a) -> AllElems c as -> AllElems c (a ': as)
consAllElems x AllElems{..} = x `withDict` (allElemsDict `withDict` allElems)

-- | Type-class of types that reify to a list of a given type.
--
-- If I remember correctly, the instance @`ReifiesList` [] a@
-- prevents a functional dependency from `as` to `a`.
class ReifiesList (as :: [k]) (a :: *) where
  reflectList :: proxy as -> [a]

instance ReifiesList ('[] :: [k]) a where
  reflectList _ = []

instance (Reifies t a, ReifiesList as a) => ReifiesList ((t :: k) ': as) a where
  reflectList xs = (reflect (headProxy xs)) : reflectList (tailProxy xs)
    where
      headProxy :: proxy (b ': bs) -> Proxy b
      headProxy _ = Proxy
      tailProxy :: proxy (b ': bs) -> Proxy bs
      tailProxy _ = Proxy

-- | Type class of types that may be compared with another of the same kind
class Compare (a :: k) where
  type Cmp (a :: k) (b :: k) :: Ordering

-- | The `Constraint` that a type-level list is strictly increasing
type family Inc (as :: [k]) :: Constraint where
  Inc '[] = ()
  Inc (x ': xs) = Inc1 x xs

-- | The tail of `Inc`
type family Inc1 (a :: k) (as :: [k]) = (result :: Constraint) | result -> a as where
  Inc1 x '[] = (x ~ x)
  Inc1 x (y ': ys) = (x ~ x, Cmp x y ~ 'LT, Inc1 y ys)

-- forall (c :: k -> Constraint). Dict (c '[]) -> (forall (a :: k) (as :: k)) Dict (c (a ': as))

-- (forall (a :: k) (as :: [k]). Dict (c a as) -> Dict (c

-- | `undefined`
inductMap ::
     (c '[] :- d '[])
  -> (forall (x :: k) (xs :: [k]). c (x ': xs) :- d (x ': xs))
  -> c ys :- d ys
inductMap _ _ = undefined

-- inductMap' ::
--      forall (k :: *) (c :: k -> [k] -> Constraint) (d :: [k] -> Constraint) (z :: k) (ws :: [k]).
--      (forall (x :: k). c x '[] :- d '[])
--   -> (forall (x :: k) (y :: k) (ys :: [k]). c x (y ': ys) :- d (y ': ys))
--   -> c z ws :- d ws
-- inductMap' _ _ = undefined

-- | `undefined`
induceMap :: forall (k :: *) (c :: [k] -> Constraint) (ys :: [k]). Dict (c '[]) -> (forall (x :: k) (xs :: [k]). Dict (c (x ': xs))) -> Dict (c (ys :: [k]))
induceMap _ _ = undefined


-- type family (a :: Inc1 x '[] :- Inc '[]) (b :: Inc1 x (y ': ys) :- Inc (y ': ys)) :: Inc z ws :- Inc ws

-- specializeInductMap ::
--      forall (k :: *) (z :: k) (ws :: [k]).
--      (forall (x :: k). Inc1 x '[] :- Inc ('[] :: [k]))
--   -> (forall (x :: k) (y :: k) (ys :: [k]). Inc1 x (y ': ys) :- Inc (y ': ys))
--   -> Inc1 z ws :- Inc ws
-- specializeInductMap = inductMap'

-- | The tail of `Inc` entails `Inc` of @[]@
tailIncEmpty :: forall a. Inc1 a '[] :- Inc '[]
tailIncEmpty = unmapDict (const Dict)

-- | The tail of I
tailIncCons :: forall (a :: k) (b :: k) (bs :: [k]). Inc1 a (b ': bs) :- Inc (b ': bs)
tailIncCons = unmapDict $ \dict -> dict `withDict` Dict


-- | In theory, we could induce on `tailIncEmpty` and `tailIncCons`...
tailInc1 :: Dict (Inc1 a as) -> Dict (Inc as)
tailInc1 = undefined -- mapDict (inductMap tailIncEmpty tailIncCons)

-- | Convert `Inc` of a non-empty type-level list to `Inc1`
incToInc1 :: Dict (Inc (a ': as)) -> Dict (Inc1 a as)
incToInc1 dict = dict `withDict` Dict

-- | Singleton `Set`s, represented on the type-level by
-- type-level strictly increasing lists
newtype Set (as :: [k]) = Set
  { setDict :: Dict (Inc as)
  } deriving (Eq, Ord, NFData)

-- | If `as` is strictly increasing, then it represents a valid `Set` of values
set :: Inc as => Set as
set = Set Dict

-- | Get the first value in a non-empty `Set`
head :: Set (a ': as) -> Proxy a
head _ = Proxy

-- | Get the tail of a non-empty `Set`
tail :: Set (a ': as) -> Set as
tail Set{..} = tailInc1 (incToInc1 setDict) `withDict` set

-- | The `Constraint` that an element of a type-level list is
-- its minimum.
type family MinOfC (a :: k) (as :: [k]) :: Constraint where
  MinOfC _ '[] = ()
  MinOfC x (y ': ys) = (Cmp x y ~ 'LT, MinOfC x ys)

-- | The singleton representing a proof that an element of
-- a type-level list is its minimum.
newtype MinOf (a :: k) (as :: [k]) = MinOf
  { minOfDict :: Dict (MinOfC a as)
  } deriving (Eq, Ord, NFData)

-- | `MinOf` may be instantiated whenever `MinOfC` holds
minOf :: MinOfC a as => MinOf a as
minOf = MinOf Dict

-- | See `MinOfC`
type family MaxOfC (a :: k) (as :: [k]) :: Constraint where
  MaxOfC _ '[] = ()
  MaxOfC x (y ': ys) = (Cmp x y ~ 'GT, MaxOfC x ys)

-- | See `MinOf`
newtype MaxOf (a :: k) (as :: [k]) = MaxOf
  { maxOfDict :: Dict (MaxOfC a as)
  } deriving (Eq, Ord, NFData)

-- | See `minOf`
maxOf :: MaxOfC a as => MaxOf a as
maxOf = MaxOf Dict

-- prepend :: MinOf a as -> Set as -> Set (a ': as)
-- prepend _ _ = set

-- | Postpend an element to a type-level list
type family Postpend (a :: k) (as :: [k]) :: [k] where
  Postpend x '[] = '[x]
  Postpend x (y ': ys) = y ': Postpend x ys

-- postpend :: MaxOf a as -> Set as -> Set (Postpend a as)
-- postpend _ _ = set

-- headIsMin :: Set (a ': as) -> MinOf a as
-- headIsMin Set{..} = setDict `withDict` minOf

-- | (Incomplete) Insert an element into a strictly increasing type-level list
type family Insert (a :: k) (as :: [k]) :: [k] where
  Insert x '[] = '[x]
  -- Insert x (y ': ys) = if x < y then (x : y : zs) elif == then (y ': ys) elif (>) then (y : Inset x ys)

-- insert :: proxy a -> Set as -> Set (Insert a as)
-- insert _ _ = set

-- | (Incomplete) Delete an element from a type-level list
type family Delete (a :: k) (as :: [k]) :: [k] where
  Delete _ '[] = '[]
  -- Insert x (y ': ys) = if x == y then ys else y ': Delete x ys

-- delete :: proxy a -> Set as -> Set (Delete a as)
-- delete _ _ = set



