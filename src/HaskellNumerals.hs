{- | HaskellNumerals : Church numerals defined outside Lambda-calculus.
-}
module HaskellNumerals (
  numeralH, succH, addH, mulH, expH
  ) where


recurse f 0 x = x
recurse f n x = f (recurse f (n-1) x)

numeralH n = \x y -> recurse x n y

expH x y = numeralH y (numeralH x)
multiplyH = (.)
successorH c a b = a (c a b)
addH_church33 n m = n successorH m
addH_rosser35 a b c d = a c (b c d)

succH n m = successorH n m succ 0
mulH  n m = (n . m) succ 0
addHC n m = addH_church33 n m succ 0
addHR n m = addH_rosser35 n m succ 0

addH n m = addHR n m 

