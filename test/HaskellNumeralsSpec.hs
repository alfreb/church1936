module HaskellNumeralsSpec (spec, testmain) where

import Test.Hspec
import Test.Hspec.QuickCheck
import Test.HUnit
import Test.QuickCheck

import HaskellNumerals

preamble = do
  putStrLn "Testing Haskell Numerals"

-- =============================================================================
--                            Haskell Numerals
-- =============================================================================

haskellNumeral_8 = expH 2 3

rep1 f n = f n
rep2 f n = f(f n)
rep3 f n = f(f(f n))
rep5 f n = f(f(f(f(f n))))
rep7 f n = f(f(f(f(f(f(f n))))))

repz f x y = f(f x y)

nary_composes1 = rep1 repz 
nary_composes2 = repz . rep1

repz :: (t1 -> t2 -> t1) -> t1 -> t2 -> t2 -> t1


prop_compositionAffectsFirstOnly = ((-) . (^2) . (^2)) 2 2 == 14



n1 = numeralH 1
n2 = numeralH 2
n3 = numeralH 3
n4 = numeralH 4

-- Composing haskellNumerals gives us multiplication.
prop_composingHaskellNumeralsGivesMultiplication =
  (n3 . n2 . n3) (+1) 0 == 3 * 2 * 3 &&
  (n2 . n3 . n4) (+1) 0 == 3 * 2 * 4 &&
  (n4 . n4 . n4) (+1) 0 == 4 * 4 * 4


-- This is captured very nicely in the type signature of our haskellNumerals:
n3 :: (t -> t) -> t -> t


three = n3 succ 0
four  = n4 succ 0

twelve  = n4 (+ (n3 succ 0)) 0
twelve' = n3 (+ (n4 succ 0)) 0

perfect f v = f v

--
-- One numeral N applied to another, M becomes M
--
-- Because:
-- 
--(No, it's only when 1 is one of them)



-- Now
prop_haskellNumeralsAreExponentialFunctions =
  n2 n2 (+1) 0 == 2^2 && 
  n2 n3 (+1) 0 == 3^2 &&
  n2 n4 (+1) 0 == 4^2 &&
  n3 n2 (+1) 0 == 2^3 &&
  True

prop_haskellNumeralsFirstParamCanMultiply =
  n2 n2 (+2) 0 == (2^2) * 2 &&
  n2 n3 (+2) 0 == (3^2) * 2 &&
  n2 n3 (+3) 0 == (3^2) * 3 &&
  n2 n4 (+3) 0 == (4^2) * 3 &&
  True



spec::Spec
spec = do
  describe "Variables" $ do
    prop "Composing numerals is multiplication" $ do
      prop_composingHaskellNumeralsGivesMultiplication
        
    prop "Haskell numerals are exponential functions when applied to successor" $ do
      prop_haskellNumeralsAreExponentialFunctions

    prop "n-adder functions act as multipliers after exponentiation " $ do
      prop_haskellNumeralsFirstParamCanMultiply 

testmain :: IO ()
testmain = hspec spec

tm = testmain
main = tm
