{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fdefer-type-errors #-} -- to allow usage of `shouldNotTypecheck`
{-# OPTIONS_GHC -Wno-deferred-type-errors #-} -- to remove warnings from `shouldNotTypecheck`

module Main where

import Control.Monad (unless)
import Data.Proxy (Proxy(..))
import Data.Reflection (Reifies(..))
import Data.Set.Symbol
import GHC.TypeLits (Symbol)
import Prelude hiding (elem, head, tail)
import System.Exit (exitFailure)
import Test.HUnit
import Test.ShouldNotTypecheck (shouldNotTypecheck)

simpleSetTypeChecks :: Test
simpleSetTypeChecks =
  test $ reflectSet (set @[ "x", "y", "z"]) @?= ["x", "y", "z"]

simpleFailureDoesntTypeCheck :: Test
simpleFailureDoesntTypeCheck =
  test $ shouldNotTypecheck (set @[ "x", "z", "y"])

typeCheckingTests :: [Test]
typeCheckingTests = [simpleSetTypeChecks, simpleFailureDoesntTypeCheck]

elemBCD ::
     Reifies (ElemList s '[ "b", "c", "d"]) Bool => proxy (s :: Symbol) -> Bool
elemBCD = (`elem` (set @[ "b", "c", "d"]))

elemTests :: [Test]
elemTests =
  fmap
    test
    [ test $ elem (Proxy @"x") (set @ '[]) @?= False
    , test $ elem (Proxy @"x") (set @ '["x"]) @?= True
    , test notElemTests
    , test isElemTests
    ]

notElemTests :: [Test]
notElemTests =
  test . (@=? False) <$>
  [ elemBCD (Proxy @"a")
  , elemBCD (Proxy @"e")
  , elemBCD (Proxy @"bb")
  , elemBCD (Proxy @"bc")
  , elemBCD (Proxy @"bd")
  ]

isElemTests :: [Test]
isElemTests =
  test . (@?= True) <$>
  [ elemBCD (Proxy @"b")
  , elemBCD (Proxy @"c")
  , elemBCD (Proxy @"d")
  ]

headTests :: [Test]
headTests =
  [ test $ shouldNotTypecheck (head (set @[]))
  , test $ head (set @ '["x"]) @?= "x"
  , test $ head (set @ '["x", "y"]) @?= "x"
  ]

tailTests :: [Test]
tailTests =
  [ test $ shouldNotTypecheck (tail (set @[]))
  , test $ reflectSet (tail (set @ '[ "x"]) :: Set '[]) @?= []
  , test $ reflectSet (tail (set @[ "x", "y"]) :: Set '["y"]) @?= ["y"]
  ]

unconsTests :: [Test]
unconsTests =
  [ test $ shouldNotTypecheck (uncons (set @[]))
  , test $
    fmap reflectSet (uncons (set @ '[ "x"]) :: (String, Set '[])) @?= ("x", [])
  , test $
    fmap reflectSet (uncons (set @[ "x", "y"]) :: (String, Set '[ "y"])) @?=
    ("x", ["y"])
  ]

tests :: [Test]
tests =
  [ test typeCheckingTests
  , test elemTests
  , test headTests
  , test tailTests
  , test unconsTests
  ]

main :: IO ()
main = do
  Counts {..} <- runTestTT (test tests)
  unless (errors == 0 && failures == 0) exitFailure

