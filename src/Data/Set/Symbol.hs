{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Set.Symbol
-- Copyright   :  (c) Michael J. Klein 2018
-- License     :  see LICENSE
--
-- Maintainer  :  lambdamichael@gmail.com
-- Stability   :  experimental
-- Portability :  non-portable (GHC Extensions)
--
-- Type-level `Set`s of `Symbol`s.
--
-- While it's possible to use this module without @TypeApplications@,
-- it is recommended.
-----------------------------------------------------------------------------

module Data.Set.Symbol (
  -- * Data types
    Set(..)

  -- * Core classes
  , IsSet
  , IsSet1
  , ReifySet(..)
  , emptyIsSet
  , insertMinIsSet
  , insertMinIsSet1
  , tailSetIsSet
  , tailSet1IsSet
  , Set1(..)
  , set1
  , emptyKnownIsSet1
  , AllKnownSym1(..)
  , Min1(..)

  -- * Construction and first operatora
  , set
  , tailIsSet
  , headIsKnown
  , headProxy
  , tail
  , unconsProxy
  , head
  , uncons
  , append
  , type (:<|>)
  , type (:<|)
  , ConsHelper
  , elem
  , ElemList
  , ElemListHelper

  -- * Operators
  , (\\)

  -- * Query
  , null
  , nullProxy
  , size
  , sizeProxy
  , Size
  , member
  , notMember
  , lookupLT
  , lookupLTProxy
  , LookupLT
  , type (:?)
  , JustIf
  , lookupGT
  , lookupGTProxy
  , LookupGT
  , lookupLE
  , lookupLEProxy
  , LookupLE
  , lookupGE
  , lookupGEProxy
  , LookupGE
  , isSubsetOf
  , isSubsetOfProxy
  , IsSubsetOf
  , isProperSubsetOf
  , isProperSubsetOfProxy
  , IsProperSubsetOf
  , disjoint
  , disjointProxy
  , Disjoint

  -- * Construction
  , empty
  , singleton
  , insert
  , delete
  , Delete
  , powerSet
  , PowerSet
  , Prepend

  -- * Combine
  , union
  , difference
  , Difference
  , intersection
  , Intersection
  , cartesianProduct
  , CartesianProduct
  , filterLT
  , FilterLT
  , filterGT
  , FilterGT
  , split
  , splitMember

  -- * Indexed
  , lookupIndex
  , lookupIndexProxy
  , LookupIndex
  , MaybeAddOne
  , findIndex
  , findIndexProxy
  , FindIndex
  , elemAt
  , elemAtProxy
  , type (<)
  , Not
  , type (/=)
  , type (&&)
  , ElemAt
  , deleteAt
  , DeleteAt
  , take
  , Take
  , drop
  , Drop
  , splitAt
  , lookupMin
  , lookupMax
  , findMin
  , findMax
  , deleteMin
  , deleteMax
  , DeleteMax
  , deleteFindMin
  , deleteFindMax
  , maxView
  , minView

  -- * Other helpers
  , liftReflect2
  ) where

import Control.DeepSeq (NFData(..))
import Control.Monad (liftM2)
import Data.Constraint ((:-)(..), Dict(..), mapDict, withDict)
import Data.Data (Data)
import Data.List (stripPrefix)
import Data.Maybe (listToMaybe, maybeToList)
import Data.Proxy (Proxy(..))
import Data.Reflection (Reifies(..))
import Data.Type.Equality
import GHC.Exts (Constraint, IsList(..))
import GHC.TypeLits
  ( type (-)
  , AppendSymbol
  , CmpSymbol
  , ErrorMessage(..)
  , KnownSymbol
  , Symbol
  , TypeError
  , symbolVal
  )
import GHC.TypeNats (type (+), type (<=?), KnownNat, Nat, natVal)
import Numeric.Natural (Natural)
import Prelude hiding (drop, elem, head, null, splitAt, tail, take)
import qualified Prelude as P

-- | Type-level sets:
--
-- @
--  λ> set :: Set '["x", "y", "z"]
--  Set ["x","y","z"]
--
--  λ> set :: Set '["x", "z", "y"]
--  <interactive>:142:1: error:
--      • Couldn't match type ‘'GT’ with ‘'LT’ arising from a use of ‘set’
--      • In the expression: set :: Set '["x", "z", "y"]
--        In an equation for ‘it’: it = set :: Set '["x", "z", "y"]
-- @
--
-- Or with @TypeApplications@ (much more concise):
--
-- @
--  λ> :t set \@["x", "y", "z"]
--  set \@["x", "y", "z"] :: Set '["x", "y", "z"]
-- @
--
newtype Set (a :: [Symbol]) = Set
  { setDict :: Dict (IsSet a)
  } deriving (Eq, Data, Ord, NFData)

-- | This is an injective type-family that asserts that a list of `Symbol`s
-- represent a valid `Set`.
type family IsSet (a :: [Symbol]) = (result :: Constraint) | result -> a where
  IsSet '[] = ()
  IsSet (x ': xs) = (KnownSymbol x, IsSet1 x xs, IsSet xs)

-- | Helper for `IsSet`, assuming a non-empty set by requiring an additional parameter.
type family IsSet1 (a :: Symbol) (as :: [Symbol]) = (result :: Constraint) | result -> a as where
  IsSet1 x '[] = KnownSymbol x
  IsSet1 x (y ': ys) = (KnownSymbol x, CmpSymbol x y ~ 'LT, IsSet (y ': ys))

-- | The empty `Set` is a `Set`
emptyIsSet :: Set '[]
emptyIsSet = set

-- | Insert a new `KnownSymbol`, that's known to be the minimum of the `Set`
insertMinIsSet :: (KnownSymbol x, IsSet1 x xs) => proxy x -> Set xs -> Set (x ': xs)
insertMinIsSet _ Set{..} = setDict `withDict` set

-- | The tail of a `Set` is a `Set`
tailSetIsSet :: Set (x ': xs) -> Set xs
tailSetIsSet Set{..} = setDict `withDict` set

-- | Non-empty `Set`
newtype Set1 (a :: Symbol) (as :: [Symbol]) = Set1
  { set1Dict :: Dict (IsSet (a ': as))
  } deriving (Eq, Data, Ord, NFData)

-- | If we know @a ': as@ represents a `Set`, we can instantiate
-- a @`Set1` a as@
set1 :: IsSet (a ': as) => Set1 a as
set1 = Set1 Dict

-- | If @x@ is a `KnownSymbol`, we can form a singleton `Set1`
emptyKnownIsSet1 :: KnownSymbol x => Set1 x '[]
emptyKnownIsSet1 = set1

-- | The tail of a `Set1` is a `Set`
tailSet1IsSet :: Set1 x xs -> Set xs
tailSet1IsSet Set1{..} = set1Dict `withDict` set

-- if forall x in xs y < x
-- then Set (y ': xs)
-- then forall x in xs

-- | The `Constraint` that a `Symbol` is the minimum of a type-level list
-- of `Symbol`s
type family IsMin (a :: Symbol) (as :: [Symbol]) :: Constraint where
  IsMin _ '[] = ()
  IsMin x (y ': ys) = (CmpSymbol x y ~ 'LT, IsMin x ys)

-- | The `Constraint` that all the `Symbol`s in a type-level list
-- of `Symbol`s are `KnownSymbol`s
type family IsAllKnownSym (as :: [Symbol]) :: Constraint where
  IsAllKnownSym '[] = ()
  IsAllKnownSym (x ': xs) = (KnownSymbol x, IsAllKnownSym xs)

-- allKnownSymSet :: Set as -> AllKnownSym as

-- allKnownSymSet1 :: Set1 a as -> AllKnownSym (a ': as)

-- | `IsAllKnownSym` for non-empty type-level lists of `Symbol`s
type family IsAllKnownSym1 (a :: Symbol) (as :: [Symbol]) :: Constraint where
  IsAllKnownSym1 x xs = (KnownSymbol x, IsAllKnownSym xs)

-- | A proof that all the `Symbol`s in the type-level list, as well
-- as the first provided `Symbol`, are all `KnownSymbol`s
newtype AllKnownSym1 (a :: Symbol) (as :: [Symbol]) = AllKnownSym1
  { allKnownSym1Dict :: Dict (IsAllKnownSym1 a as)
  } deriving (Eq, Data, Ord, NFData)

-- allKnownSym1Set :: Set (a ': as) -> AllKnownSym1 a as

-- allKnownSym1Set1 :: Set1 a as -> AllKnownSym a as


-- | `Min1` encodes a non-empty `AllKnownSym1` `Set1`
newtype Min1 (a :: Symbol) (as :: [Symbol]) = Min1
  { min1Dict :: Dict (IsMin a as)
  } deriving (Eq, Data, Ord, NFData)


-- allKnownSymSet :: Set a

-- | We have a bijection between `Min1` and `Set1` when we have `AllKnownSym1`
-- fromMin1 :: (AllKnownSym1 x xs, Min1 x xs, Set xs) :- Set1 x xs
-- fromMin1 =

-- toMin1 :: Set1 x xs :- Min1 x xs
-- toMin1 = _

-- | Insert a new minimum `KnownSymbol` into a `Set1`
insertMinIsSet1 :: (KnownSymbol x, CmpSymbol x y ~ 'LT) => proxy x -> Set1 y ys -> Set1 x (y ': ys)
insertMinIsSet1 _ Set1{..} = set1Dict `withDict` set1



-- | Since `Set`s are determined by their type, and so they're always equal,
-- @(`<>`)@ simply returns the set of the given type.
--
-- Note: @(`<>`)@ is actually equivalent to _both_ `intersection` and `union`!
-- (Because they're always equal xD)
instance IsSet s => Semigroup (Set s) where
  (<>) _ _ = set

-- | Since `Set`s are determined by their type, and so they're always equal,
-- `mempty` is the set of the given type and
-- @(`mappend`)@ simply returns `mempty`.
instance IsSet s => Monoid (Set s) where
  mempty = set
  mappend _ _ = set

-- | Uses `reflectSet`
instance ReifySet a => Show (Set a) where
  show = ("Set " ++) . show . reflectSet

-- Since @`Set` a@ is a singleton type, we can `read` it easily:
--
-- @
--  λ> read @(Set '["x", "y", "z"]) (show (set @["x", "y", "z"]))
--  Set ["x","y","z"]
--
--  λ> read @(Set '["x", "y", "zs"]) (show (set @["x", "y", "z"]))
--  Set ["*** Exception: Prelude.read: no parse
-- @
--
instance (ReifySet a, IsSet a) => Read (Set a) where
  readsPrec _ = fmap (set', ) . maybeToList . stripPrefix (show set')
    where
      set' = set

-- | The class of lists of symbols that can be reflected from a `Set`
class ReifySet (a :: [Symbol]) where
  reflectSet :: Set a -> [String]

-- | Base case
instance ReifySet '[] where
  reflectSet _ = []

-- | Induction case
instance ReifySet as => ReifySet (a ': as) where
  reflectSet = uncurry (:) . fmap reflectSet . uncons

-- | Example:
--
-- @
--  λ> ["x", "y", "z"] :: Set '["x", "y", "z"]
--  Set ["x","y","z"]
-- @
--
instance (ReifySet a, IsSet a) => IsList (Set a) where
  type Item (Set a) = String
  fromList xs =
    if ysList == xs
      then ys
      else error . unlines $
           [ "Invalid Set:"
           , "Expected:"
           , showStrings ysList
           , "But got:"
           , showStrings xs
           ]
    where
      ys = set `asTypeOf` fromList xs
      ysList = toList ys
      showStrings = unlines . fmap ("  " ++)
  toList = reflectSet

-- | Construct a `Set` using its type, e.g.
--
-- @
--  λ> set :: Set '["x", "y", "z"]
--  Set ["x","y","z"]
-- @
--
-- Or with @TypeApplications@ (much more concise):
--
-- @
--  λ> set \@["x", "y", "z"]
--  Set ["x", "y", "z"]
-- @
--
set :: IsSet a => Set a
set = Set Dict

-- | A proof that the `tail` of a `Set` is a `Set`
tailIsSet :: IsSet (a ': as) :- IsSet as
tailIsSet = Sub Dict

-- | A proof that the `head` of a `Set` is a `KnownSymbol`
headIsKnown :: IsSet (x ': xs) :- KnownSymbol x
headIsKnown = Sub Dict

-- | Type-level `head`
headProxy :: Set (a ': as) -> Proxy a
headProxy = const Proxy

-- | Extract the elements after the `head` of a `Set`, which is non-empty
tail :: Set (a ': as) -> Set as
tail Set {..} = mapDict tailIsSet setDict `withDict` set

-- | Type-level `uncons`
unconsProxy :: Set (a ': as) -> (Proxy a, Set as)
unconsProxy = liftM2 (,) headProxy tail

-- | Extract the first (least) element of a list, which is non-empty.
head :: Set (a ': as) -> String
head set'@Set {..} =
  mapDict headIsKnown setDict `withDict` symbolVal (headProxy set')

-- | Decompose a `Set` into its `head` and `tail`.
uncons :: Set (a ': as) -> (String, Set as)
uncons = liftM2 (,) head tail

-- TODO: rename to `union`
--
-- - derive that: forall (a :: Symbol). IsSet as :- IsSet (a :<| as)
-- - derive that: (IsSet as, IsSet bs) :- IsSet (as :<|> bs)
-- | Append two sets
--
-- @
--  λ> set @ '["x", "y"] \``append`\` set @ '["z"]
--  Set ["x","y","z"]
-- @
--
append :: IsSet (a :<|> b) => Set a -> Set b -> Set (a :<|> b)
append _ _ = set

infixl 3 :<|>

-- | Append two `Symbol` lists that represent `Set`s
type family (:<|>) (a :: [Symbol]) (b :: [Symbol]) = (result :: [Symbol]) where
  '[] :<|> y = y
  x :<|> '[] = x
  (x : xs) :<|> ys = x :<| xs :<|> ys

infixl 2 :<|

-- | Insert a `Symbol` into a `Symbol` list of a `Set`
type family (:<|) (a :: Symbol) (b :: [Symbol]) :: [Symbol] where
  x :<| '[] = '[ x]
  x :<| (y : ys) = ConsHelper (CmpSymbol x y) x y ys

-- | a b result -> c, a b result -> bs, a c result -> b
type family ConsHelper (c :: Ordering) (a :: Symbol) (b :: Symbol) (bs :: [Symbol]) :: [Symbol] where
  ConsHelper 'LT x y ys = x : y : ys
  ConsHelper 'EQ x y ys = y : ys
  ConsHelper 'GT x y ys = y : (x :<| ys)

-- | Is a `Symbol` an `elem` of the given `Set`?
--
-- @
--  λ> elem (Proxy @"y") (set @ '["x","y","z"])
--  True
--
--  λ> elem (Proxy @"y") (set @ '["x","z"])
--  False
-- @
--
elem :: Reifies (ElemList s a) Bool => proxy (s :: Symbol) -> Set a -> Bool
elem x xs = reflect $ elemProxy x xs
  where
    elemProxy :: proxy' b -> Set bs -> Proxy (ElemList b bs)
    elemProxy _ _ = Proxy

-- | The type family behind `elem`
type family ElemList (a :: Symbol) (as :: [Symbol]) :: Bool where
  ElemList _ '[] = 'False
  ElemList x (y ': ys) = ElemListHelper (CmpSymbol x y) x y ys

-- | `ElemList` assuming non-empty and with known `Ordering`
type family ElemListHelper (c :: Ordering) (a :: Symbol) (b :: Symbol) (as :: [Symbol]) :: Bool where
  ElemListHelper 'GT x _ ys = ElemList x ys
  ElemListHelper 'EQ _ _ _ = 'True
  ElemListHelper 'LT _ _ _ = 'False

--------- BEGIN Data.Set Functions -----------

-- * Operators

-- | Alias for `difference`
(\\) :: IsSet (Difference a b) => Set a -> Set b -> Set (Difference a b)
(\\) = difference

-- * Query

-- | Is this the empty `Set`?
null :: Reifies (a == '[]) Bool => Set a -> Bool
null = reflect . nullProxy

-- | Type-level implementation of `null`
nullProxy :: Set a -> Proxy (a == '[])
nullProxy _ = Proxy

-- | The number of elements in the `Set`.
size :: KnownNat (Size a) => Set a -> Natural
size = natVal . sizeProxy

-- | Type-level `size`
sizeProxy :: Set a -> Proxy (Size a)
sizeProxy _ = Proxy

-- | Type family encoding of `size`
type family Size (as :: [Symbol]) :: Nat where
  Size '[] = 0
  Size (_ ': as) = 1 + Size as

-- | Is the element in the `Set`?
member :: Reifies (ElemList s a) Bool => proxy (s :: Symbol) -> Set a -> Bool
member = elem

-- | Is the element not in the `Set`?
notMember :: Reifies (ElemList s a) Bool => proxy (s :: Symbol) -> Set a -> Bool
notMember = fmap not . member

-- | Find largest element smaller than the given one.
--
-- @
--  lookupLT 3 (fromList [3, 5]) == Nothing
--  lookupLT 5 (fromList [3, 5]) == Just 3
-- @
--
lookupLT ::
     Reifies (LookupLT a as) (Maybe String)
  => proxy (a :: Symbol)
  -> Set as
  -> Maybe String
lookupLT = fmap reflect . lookupLTProxy

-- | Type-level `lookupLT`
lookupLTProxy ::
     proxy (a :: Symbol) -> Set as -> Proxy (LookupLT a as :: Maybe Symbol)
lookupLTProxy _ _ = Proxy

-- | Type family encoding of `lookupLT`
type family LookupLT (a :: Symbol) (as :: [Symbol]) :: Maybe Symbol where
  LookupLT _ '[] = 'Nothing
  LookupLT x '[ y] = JustIf y (CmpSymbol x y == 'LT)
  LookupLT x (y ': z ': ws) = (((CmpSymbol x y == 'LT) && (CmpSymbol x z /= 'LT)) :? (LookupLT x (z ': ws))) ('Just y)

-- | Type family encoding of the ternary operator
-- (if `False` then first argument else second)
type family (:?) (a :: Bool) (b :: k) (c :: k) :: k where
  (:?) 'False x _ = x
  (:?) 'True _ y = y

-- | Type family encoding of:
--
-- @
--  \x b ->
--    if b
--      then Just x
--      else Nothing
-- @
--
type family JustIf (a :: Symbol) (b :: Bool) :: Maybe Symbol where
  JustIf x b = (b :? 'Nothing) ('Just x)

-- | Find smallest element greater than the given one.
--
-- @
--  lookupGT 4 (fromList [3, 5]) == Just 5
--  lookupGT 5 (fromList [3, 5]) == Nothing
-- @
--
lookupGT ::
     Reifies (LookupGT a as) (Maybe String)
  => proxy (a :: Symbol)
  -> Set as
  -> Maybe String
lookupGT = fmap reflect . lookupGTProxy

-- | Type-level `lookupGT`
lookupGTProxy ::
     proxy (a :: Symbol) -> Set as -> Proxy (LookupGT a as :: Maybe Symbol)
lookupGTProxy _ _ = Proxy

-- | Type family encoding of `lookupGT`
type family LookupGT (a :: Symbol) (as :: [Symbol]) :: Maybe Symbol where
  LookupGT _ '[] = 'Nothing
  LookupGT x (y ': ys) = ((CmpSymbol x y == 'LT) :? (LookupGT x ys)) ('Just y)

-- | Find largest element smaller or equal to the given one.
--
-- @
--  lookupLE 2 (fromList [3, 5]) == Nothing
--  lookupLE 4 (fromList [3, 5]) == Just 3
--  lookupLE 5 (fromList [3, 5]) == Just 5
-- @
--
lookupLE ::
     Reifies (LookupLE a as) (Maybe String)
  => proxy (a :: Symbol)
  -> Set as
  -> Maybe String
lookupLE = fmap reflect . lookupLEProxy

-- | Type-level `lookupLE`
lookupLEProxy ::
     proxy (a :: Symbol) -> Set as -> Proxy (LookupLE a as :: Maybe Symbol)
lookupLEProxy _ _ = Proxy

-- | Type family encoding of `lookupLE`
type family LookupLE (a :: Symbol) (as :: [Symbol]) :: Maybe Symbol where
  LookupLE _ '[] = 'Nothing
  LookupLE x '[ y] = JustIf y (CmpSymbol y x /= 'GT)
  LookupLE x (y ': z ': ws) = (((CmpSymbol y x /= 'GT) && (CmpSymbol x z == 'LT)) :? (LookupLE x (z ': ws))) ('Just y)

-- | Find smallest element greater or equal to the given one.
--
-- @
--  lookupGE 3 (fromList [3, 5]) == Just 3
--  lookupGE 4 (fromList [3, 5]) == Just 5
--  lookupGE 6 (fromList [3, 5]) == Nothing
-- @
--
lookupGE ::
     Reifies (LookupGE a as) (Maybe String)
  => proxy (a :: Symbol)
  -> Set as
  -> Maybe String
lookupGE = fmap reflect . lookupGEProxy

-- | Type-level `lookupGE`
lookupGEProxy ::
     proxy (a :: Symbol) -> Set as -> Proxy (LookupGE a as :: Maybe Symbol)
lookupGEProxy _ _ = Proxy

-- | Type family encoding of `LookupGE`
type family LookupGE (a :: Symbol) (as :: [Symbol]) :: Maybe Symbol where
  LookupGE _ '[] = 'Nothing
  LookupGE x (y ': ys) = ((CmpSymbol x y /= 'GT) :? (LookupGE x ys)) ('Just y)

-- | Is this a subset? @(s1 `isSubsetOf` s2) tells whether @s1@ is a subset of @s2@.
isSubsetOf :: Reifies (IsSubsetOf a b) Bool => Set a -> Set b -> Bool
isSubsetOf = liftReflect2 isSubsetOfProxy

-- | Type-level `isSubsetOf`
isSubsetOfProxy :: Set a -> Set b -> Proxy (IsSubsetOf a b :: Bool)
isSubsetOfProxy _ _ = Proxy

-- | Type family encoding of `isSubsetOf`
type family IsSubsetOf (a :: [Symbol]) (b :: [Symbol]) :: Bool where
  IsSubsetOf '[] _ = 'True
  IsSubsetOf (x ': xs) ys = ElemList x ys && IsSubsetOf xs ys

-- | Is this a proper subset? (ie. a subset but not equal).
isProperSubsetOf ::
     Reifies (IsSubsetOf a b && Not (a == b)) Bool => Set a -> Set b -> Bool
isProperSubsetOf = liftReflect2 isProperSubsetOfProxy

-- | Type-level `isProperSubsetOf`
isProperSubsetOfProxy :: Set a -> Set b -> Proxy (IsProperSubsetOf a b :: Bool)
isProperSubsetOfProxy _ _ = Proxy

-- | Type family encoding of `isProperSubsetOf`
type family IsProperSubsetOf (a :: [Symbol]) (b :: [Symbol]) :: Bool where
  IsProperSubsetOf xs ys = IsSubsetOf xs ys && Not (xs == ys)

-- | Check whether two `Set`s are disjoint (i.e. their intersection is `empty`).
--
-- @
--  disjoint (fromList [2,4,6])   (fromList [1,3])     == True
--  disjoint (fromList [2,4,6,8]) (fromList [2,3,5,7]) == False
--  disjoint (fromList [1,2])     (fromList [1,2,3,4]) == False
--  disjoint (fromList [])        (fromList [])        == True
-- @
--
disjoint :: Reifies (Intersection a b == '[]) Bool => Set a -> Set b -> Bool
disjoint = liftReflect2 disjointProxy

-- | Type-level `disjoint`
disjointProxy :: Set a -> Set b -> Proxy (Disjoint a b :: Bool)
disjointProxy _ _ = Proxy

-- | Type family encoding of `disjoint`
type family Disjoint (a :: [Symbol]) (b :: [Symbol]) :: Bool where
  Disjoint xs ys = Intersection xs ys == '[]

-- * Construction

-- | The empty `Set`.
empty :: Set '[]
empty = set

-- | Construct a `Set` containing a single element
singleton :: KnownSymbol a => proxy (a :: Symbol) -> Set '[ a]
singleton _ = set

-- | Insert an element in a set.
-- If the set already contains an element equal to the given value,
-- it is replaced with the new value.
insert :: IsSet (a ': as) => proxy (a :: Symbol) -> Set as -> Set (a ': as)
insert _ _ = set

-- | Delete an element from a set.
delete ::
     IsSet (Delete a as) => proxy (a :: Symbol) -> Set as -> Set (Delete a as)
delete _ _ = set

-- | Type family encoding of `delete`
type family Delete (a :: Symbol) (as :: [Symbol]) :: [Symbol] where
  Delete _ '[] = '[]
  Delete x (y ': ys) = ((x == y) :? (y ': Delete x ys)) ys

-- | We do:
--
-- @
--  powerset someSet = Set [concat subset | subset <- toList (powerSet someSet)]
-- @
--
powerSet :: IsSet (PowerSet a) => Set a -> Set (PowerSet a)
powerSet _ = set

-- | Type family encoding of `powerSet`
type family PowerSet (a :: [Symbol]) = (result :: [Symbol]) where
  PowerSet '[] = '[]
  PowerSet (x ': xs) = PowerSet xs :<|> PowerSet (Prepend x xs)

-- | Prepend the given `Symbol` to all elements of the list (preserves order)
type family Prepend (a :: Symbol) (as :: [Symbol]) = (result :: [Symbol]) where
  Prepend _ '[] = '[]
  Prepend x (y ': ys) = (x `AppendSymbol` y) ': Prepend x ys

-- * Combine

-- | The union of two sets
union :: IsSet (a :<|> b) => Set a -> Set b -> Set (a :<|> b)
union = append

-- | Difference of two `Set`s.
difference :: IsSet (Difference a b) => Set a -> Set b -> Set (Difference a b)
difference _ _ = set

-- | Type family encoding of `difference`
type family Difference (a :: [Symbol]) (b :: [Symbol]) :: [Symbol] where
  Difference '[] _ = '[]
  Difference xs '[] = xs
  Difference xs (y ': ys) = Difference (Delete y xs) ys

-- | The intersection of two `Set`s.
intersection ::
     IsSet (Intersection a b) => Set a -> Set b -> Set (Intersection a b)
intersection _ _ = set

-- | Type family encoding of `intersection`
type family Intersection (a :: [Symbol]) (b :: [Symbol]) :: [Symbol] where
  Intersection '[] _ = '[]
  Intersection (x ': xs) ys = ((ElemList x ys) :? (Intersection xs ys)) (x ': Intersection xs ys)

-- | Calculate the Cartesian product of two `Set`s.
-- Since there are no tuples, the elements are appended
-- instead of paired in the result.
--
-- @
--  cartesianProduct xs ys = fromList $ liftA2 (,) (toList xs) (toList ys)
-- @
--
-- Example:
--
-- @
--  cartesianProduct (fromList [1,2]) (fromList [a,b]) =
--    fromList [(1,a), (1,b), (2,a), (2,b)]
-- @
--
cartesianProduct ::
     IsSet (CartesianProduct a b)
  => Set a
  -> Set b
  -> Set (CartesianProduct a b)
cartesianProduct _ _ = set

-- | Type family encoding of `cartesianProduct`
type family CartesianProduct (a :: [Symbol]) (b :: [Symbol]) :: [Symbol] where
  CartesianProduct '[] _ = '[]
  CartesianProduct (x ': xs) ys = Prepend x ys :<|> CartesianProduct xs ys

-- Helper for `CartesianProduct` where the first argument
-- type family CartesianProduct1 (a :: Symbol) (b :: [Symbol]) :: [Symbol] where
--   CartesianProduct1 _ '[] = '[]
--   CartesianProduct1 x (y ': ys) = (x `AppendSymbol` y) ': CartesianProduct1 x ys
-- Not sure if possible
-- Calculate the disjoin union of two `Set`s.
-- disjointUnion :: IsSet (DisjointUnion a b) => Set a -> Set b -> Set (DisjointUnion a b)
-- disjointUnion _ _ = set

-- | Only retain elements less than the given one
filterLT ::
     IsSet (FilterLT a as)
  => proxy (a :: Symbol)
  -> Set as
  -> Set (FilterLT a as)
filterLT _ _ = set

-- | Type family encoding of `filterLT`
type family FilterLT (a :: Symbol) (as :: [Symbol]) :: [Symbol] where
  FilterLT _ '[] = '[]
  FilterLT x (y ': ys) = ((CmpSymbol x y == 'GT) :? '[]) (y ': FilterLT x ys)

-- | Only retain elements greater than the given one
filterGT ::
     IsSet (FilterGT a as)
  => proxy (a :: Symbol)
  -> Set as
  -> Set (FilterGT a as)
filterGT _ _ = set

-- | Type family encoding of `filterGT`
type family FilterGT (a :: Symbol) (as :: [Symbol]) :: [Symbol] where
  FilterGT _ '[] = '[]
  FilterGT x (y ': ys) = ((CmpSymbol x y == 'LT) :? (FilterGT x ys)) (y ': ys)

-- | The expression (split x set) is a pair (set1,set2) where set1 comprises the elements of set less than x and set2 comprises the elements of set greater than x
split :: (IsSet (FilterLT a as), IsSet (FilterGT a as)) => proxy (a :: Symbol) -> Set as -> (Set (FilterLT a as), Set (FilterGT a as))
split x xs = (filterLT x xs, filterGT x xs)

-- | Performs a split but also returns whether the pivot element was found in the original set.
splitMember :: (IsSet (FilterLT a as), Reifies (ElemList a as) Bool, IsSet (FilterGT a as)) => proxy (a :: Symbol) -> Set as -> (Set (FilterLT a as), Bool, Set (FilterGT a as))
splitMember x xs = (filterLT x xs, elem x xs, filterGT x xs)

-- * Indexed

-- | Lookup the index of an element, which is its zero-based index in the sorted sequence of elements. The index is a number from 0 up to, but not including, the size of the set.
--
-- @
--  isJust   (lookupIndex 2 (fromList [5,3])) == False
--  fromJust (lookupIndex 3 (fromList [5,3])) == 0
--  fromJust (lookupIndex 5 (fromList [5,3])) == 1
--  isJust   (lookupIndex 6 (fromList [5,3])) == False
-- @
--
lookupIndex ::
     Reifies (LookupIndex a as) (Maybe Natural)
  => proxy (a :: Symbol)
  -> Set as
  -> Maybe Natural
lookupIndex = fmap reflect . lookupIndexProxy

-- | Type-level `lookupIndex`
lookupIndexProxy ::
     proxy (a :: Symbol) -> Set as -> Proxy (LookupIndex a as :: Maybe Nat)
lookupIndexProxy _ _ = Proxy

-- | Type family encoding of `lookupIndex`
type family LookupIndex (a :: Symbol) (as :: [Symbol]) :: Maybe Nat where
  LookupIndex _ '[] = 'Nothing
  LookupIndex x (y ': ys) = ((x == y) :? (MaybeAddOne (LookupIndex x ys))) ('Just 0)

-- | Equivalent to @`fmap` (`+` 1)@
type family MaybeAddOne (a :: Maybe Nat) = (result :: Maybe Nat) where
  MaybeAddOne 'Nothing = 'Nothing
  MaybeAddOne ('Just x) = 'Just (x + 1)

-- | Return the index of an element, which is its zero-based index in the sorted sequence of elements.
-- The index is a number from 0 up to, but not including, the size of the set.
--
-- @
--  findIndex 2 (fromList [5,3])    Error: element is not in the set
--  findIndex 3 (fromList [5,3]) == 0
--  findIndex 5 (fromList [5,3]) == 1
--  findIndex 6 (fromList [5,3])    Error: element is not in the set
-- @
--
findIndex ::
     (KnownNat (FindIndex a as), ElemList a as ~ 'True)
  => proxy (a :: Symbol)
  -> Set as
  -> Natural
findIndex = fmap natVal . findIndexProxy

-- | Type-level `findIndex`
findIndexProxy ::
     (KnownNat (FindIndex a as), ElemList a as ~ 'True)
  => proxy (a :: Symbol)
  -> Set as
  -> Proxy (FindIndex a as)
findIndexProxy _ _ = Proxy

-- | Type family encoding of `findIndex`
type family FindIndex (a :: Symbol) (as :: [Symbol]) :: Nat where
  FindIndex x (y ': ys) = ((x == y) :? (1 + FindIndex x ys)) 0
  FindIndex _ _ = TypeError ('Text "Impossible case, did you drop the ElemList constraint?")

-- | Retrieve an element by its index, i.e. by its zero-based index in the sorted sequence of elements. If the index is out of range (less than zero, greater or equal to size of the set), error is called.
--
-- @
--  elemAt 0 (fromList [5,3]) == 3
--  elemAt 1 (fromList [5,3]) == 5
--  elemAt 2 (fromList [5,3])    Error: index out of range
-- @
--
elemAt ::
     (i < Size a ~ 'True, KnownSymbol (ElemAt i a))
  => proxy (i :: Nat)
  -> Set a
  -> String
elemAt = liftReflect2 elemAtProxy

-- | Type-level `elemAt`
elemAtProxy ::
     (i < Size a ~ 'True)
  => proxy (i :: Nat)
  -> Set a
  -> Proxy (ElemAt i a :: Symbol)
elemAtProxy _ _ = Proxy

-- | Type family representing less than
type family (<) (a :: Nat) (b :: Nat) :: Bool where
  (<) x y = (x <=? y) && Not (x == y)

-- | Type level `not`
type family Not (a :: Bool) = (res :: Bool) | res -> a where
  Not 'False = 'True
  Not 'True = 'False

-- | Type level @(`/=`)@
type family (/=) (a :: k) (b :: k) :: Bool where
  x /= y = Not (x == y)

-- | Tyoe level @(`&&`)@
type family (&&) (a :: Bool) (b :: Bool) where
  (&&) 'True 'True = 'True
  (&&) _ _ = 'False

-- | Type family encoding of `elemAt`
type family ElemAt (i :: Nat) (a :: [Symbol]) :: Symbol where
  ElemAt 0 (x ': _) = x
  ElemAt i (_ ': xs) = ElemAt (i - 1) xs
  ElemAt _ _ = TypeError ('Text "Impossible case:" ':$$: 'Text "Unless you applied ElemAt without the cooresponding `i < Size a` requirement")

-- | Delete the element at index, i.e. by its zero-based index in the sorted sequence of elements. If the index is out of range (less than zero, greater or equal to size of the set), error is called.
--
-- @
--  deleteAt 0    (fromList [5,3]) == singleton 5
--  deleteAt 1    (fromList [5,3]) == singleton 3
--  deleteAt 2    (fromList [5,3])    Error: index out of range
--  deleteAt (-1) (fromList [5,3])    Error: index out of range
-- @
--
deleteAt ::
     IsSet (DeleteAt i a) => proxy (i :: Nat) -> Set a -> Set (DeleteAt i a)
deleteAt _ _ = set

-- | Type family encoding of `deleteAt`
type family DeleteAt (i :: Nat) (a :: [Symbol]) :: [Symbol] where
  DeleteAt _ '[] = '[]
  DeleteAt 0 (_ ': xs) = xs
  DeleteAt i (x ': xs) = x ': DeleteAt (i - 1) xs

-- | Take a given number of elements in order, beginning with the smallest ones.
take :: IsSet (Take i a) => proxy (i :: Nat) -> Set a -> Set (Take i a)
take _ _ = set

-- | Type family encoding of `take`
type family Take (i :: Nat) (a :: [Symbol]) :: [Symbol] where
  Take 0 _ = '[]
  Take _ '[] = '[]
  Take i (x ': xs) = x ': Take (i - 1) xs

-- | Drop a given number of elements in order, beginning with the smallest ones.
drop :: IsSet (Drop i a) => proxt (i :: Nat) -> Set a -> Set (Drop i a)
drop _ _ = set

-- | Type family encoding of `drop`
type family Drop (i :: Nat) (a :: [Symbol]) :: [Symbol] where
  Drop 0 xs = xs
  Drop _ '[] = '[]
  Drop i (_ ': xs) = Drop (i - 1) xs

-- | Split a set at a particular index.
--
-- @
--  splitAt n xs = (take n xs, drop n xs)
-- @
--
splitAt ::
     (IsSet (Take i a), IsSet (Drop i a))
  => proxy (i :: Nat)
  -> Set a
  -> (Set (Take i a), Set (Drop i a))
splitAt _ _ = (set, set)

-- | The minimal element of a set.
lookupMin :: ReifySet a => Set a -> Maybe String
lookupMin = listToMaybe . reflectSet

-- | The maximal element of a set.
lookupMax :: ReifySet a => Set a -> Maybe String
lookupMax = listToMaybe . reverse . reflectSet

-- | The minimal element of a set.
findMin :: ReifySet (a ': as) => Set (a ': as) -> String
findMin = P.head . reflectSet

-- | The maximal element of a set.
findMax :: ReifySet (a ': as) => Set (a ': as) -> String
findMax = P.head . reverse . reflectSet

-- | Delete the minimal element. Returns an empty set if the set is empty.
deleteMin :: Set (a ': as) -> Set as
deleteMin = tail

-- | Delete the maximal element. Returns an empty set if the set is empty.
deleteMax :: IsSet (DeleteMax a) => Set a -> Set (DeleteMax a)
deleteMax _ = set

-- | Type family encoding of `deleteMax`
type family DeleteMax (a :: [Symbol]) :: [Symbol] where
  DeleteMax '[] = '[]
  DeleteMax '[ _] = '[]
  DeleteMax (_ ': x ': xs) = DeleteMax (x ': xs)

-- | Delete and find the minimal element.
-- deleteFindMin set = (findMin set, deleteMin set)
deleteFindMin :: Set (a ': as) -> (String, Set as)
deleteFindMin = uncons

-- | Delete and find the maximal element.
-- deleteFindMax set = (findMax set, deleteMax set)
deleteFindMax ::
     (IsSet (DeleteMax (a ': as)), ReifySet (a ': as))
  => Set (a ': as)
  -> (String, Set (DeleteMax (a ': as)))
deleteFindMax = liftM2 (,) findMax deleteMax

-- | Retrieves the maximal key of the set, and the set stripped of that element, or Nothing if passed an empty set.
maxView ::
     (IsSet (DeleteMax a), ReifySet a)
  => Set a
  -> Maybe (String, Set (DeleteMax a))
maxView = liftM2 (liftM2 (,)) lookupMax (return . deleteMax)

-- | Retrieves the minimal key of the set, and the set stripped of that element, or Nothing if passed an empty set.
minView :: ReifySet (a ': as) => Set (a ': as) -> Maybe (String, Set as)
minView = liftM2 (liftM2 (,)) lookupMin (return . deleteMin)

-- * Other helpers

-- | Lift a function returning a type that we can `reflect`
liftReflect2 :: Reifies s c => (a -> b -> proxy s) -> a -> b -> c
liftReflect2 = (fmap reflect .)

instance Reifies (s :: k) a =>
         Reifies '( ('Proxy :: Proxy a), ('Nothing :: Maybe k)) (Maybe a) where
  reflect _ = Nothing

instance Reifies (s :: k) a =>
         Reifies '( ('Proxy :: Proxy a), ('Just s :: Maybe k)) (Maybe a) where
  reflect = Just . reflect . fromJustSndProxy
    where
      fromJustSndProxy :: proxy '( x, 'Just y) -> Proxy y
      fromJustSndProxy _ = Proxy

instance Reifies 'True Bool where
  reflect _ = True

instance Reifies 'False Bool where
  reflect _ = False

