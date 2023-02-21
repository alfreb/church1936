module Church1936Spec (spec, testmain) where

import Test.Hspec
import Test.Hspec.QuickCheck
import Test.HUnit
import Test.QuickCheck

import Church1936 as C36

preamble = do
  putStrLn "Testing Church's Lambda calculus"


varExamples = [
  "a", "b", "c", "x", "y", "z",
  "a₁", "b₂", "c₉", "x₄₂","y₉₉", "z₇₈₉" ]

num0 = Lambda va (Lambda vb _b)
num4 = reduceFully $ Pair successor num3
snum1 = (Pair successor num1)
snum2 = (Pair successor snum1)

formula1 = (Lambda vx (Lambda vy (Pair _x _y)))

prop_numerals_valid (Positive n) = fromNumeral(toNumeral n) == n

-- Helper variables
va = var "a"
vb = var "b"
vc = var "c"
vd = var "d"
vf = var "f"
vi = var "i"
vk = var "k"
vm = var "m"
vn = var "n"
vx = var "x"
vy = var "y"
vz = var "z"


_a = toVar "a"
_b = toVar "b"
_c = toVar "c"
_n = toVar "n"
_m = toVar "m"
_x = toVar "x"
_y = toVar "y"
_z = toVar "z"


spec::Spec
spec = do
  describe "Variables" $ do
    describe "There are infinite variables, starting with 'a', 'b', 'c'" $ do
      it "Church doesnt't name the succesor of 'z' so we'll pick 'a₁'" $ do
        (succ $ var "z") `shouldBe` var "a₁"
      describe "The Enum class provides a total ordering for Variables:" $ do
        it "after a₁, b₁" $ do
          (succ $ succ $ var "z") `shouldBe` (var "b₁")
        it "after x₁, y₁" $ do
          (succ $ var "x₁") `shouldBe` var "y₁"
        it "after z₁, a₂" $ do
          (succ $ var "z₁") `shouldBe` var "a₂"
        it "after a₂, b₂" $ do
          (succ $ var "a₂") `shouldBe` var "b₂"
        it "after z₂, a₃" $ do
          (succ $ var "z₂") `shouldBe` var "a₃"
        it "z₁ < b₂" $ do
          (var "z₁") < (var "b₂") `shouldBe` True        
        it "z₁ > b₁" $ do
          (var "z₁") > (var "b₁") `shouldBe` True
          
        it "This also gives us a helpful list generator for variables" $ do
          [var "a"..] !! 26 `shouldBe` var "a₁"
          [var "a"..] !! (26 * 2) `shouldBe` var "a₂"
    
    it "Lowercase letters with and without subscript indices are variables" $ do
      (and $ map isVariableStr varExamples) `shouldBe` True
    
    it "Variables standing alone are free" $ do
      isFree vx (Var vx) `shouldBe` True

    it "x and y are free variables in the pair {x}(y)" $ do
      let f = Pair (toVar "x") (toVar "y") in
        isFree vx f
        && isFree vy f

    it "The free variables in 𝝺x . x(𝝺z . b(z)) are [b]" $ do 
      (freeVars $ Lambda vx (Pair _x (Lambda vz (Pair _b _z))))
        `shouldBe` [var "b"]
        
    it "x is bound in 𝝺x.x" $ do
      isFree vx (Lambda vx (Var vx)) `shouldBe` False
      isBound vx (Lambda vx (Var vx)) `shouldBe` True

    it "The bound vars in 𝝺ab . a(b) is [a,b]" $ do
      boundVars num1 `shouldBe` [var "a", var "b"]

    it "The bound vars in 𝝺ab . b is [b]" $ do
      boundVars (Lambda va (Lambda vb _b))
        `shouldBe` [var "b"]

    it "The bound vars in 𝝺ab . a is [a]" $ do
      boundVars (Lambda va (Lambda vb _a))
        `shouldBe` [var "a"] 

  describe "Formula abbreviation. " $ do
      it "We can generate abbreviated and non-abbreviated formulas" $ do
        abbreviate ON  formula1 `shouldBe` "𝝺xy . x(y)"
        abbreviate OFF formula1 `shouldBe` "𝝺x[𝝺y[{x}(y)]]"
        abbreviate OFF num1 `shouldBe` "𝝺a[𝝺b[{a}(b)]]" 
        abbreviate ON  num1 `shouldBe` "𝝺ab . a(b)"
        abbreviate OFF num2 `shouldBe` "𝝺a[𝝺b[{a}({a}(b))]]" 
        abbreviate ON  num2 `shouldBe` "𝝺ab . a(a(b))"  
        abbreviate OFF num3 `shouldBe` "𝝺a[𝝺b[{a}({a}({a}(b)))]]" 
        abbreviate ON  num3 `shouldBe` "𝝺ab . a(a(a(b)))"
        
  describe "Church numerals" $ do
    it "Are lambda's of two parameters, with nested pairs of variables" $ do
      Lambda va (Lambda vb (Pair _a _b)) `shouldBe` num1
      Lambda va (Lambda vb (Pair _a (Pair _a _b))) `shouldBe` num2
      Lambda va (Lambda vb (Pair _a (Pair _a (Pair _a _b)))) `shouldBe` num3

    it "The nesting is a right fold" $ do
      Lambda va (Lambda vb (foldr Pair _b [_a, _a, _a, _a, _a, _a, _a]))
        `shouldBe` toNumeral 7
      Lambda va (Lambda vb (foldl Pair _b [_a, _a, _a, _a, _a, _a, _a]))
        `shouldNotBe` toNumeral 7
    
    prop "Can be generated from numeric values and back to formulas"
      $ \(Positive n) -> fromNumeral(toNumeral n) `shouldBe` (n :: Int)
      
  describe "Successor" $ do
    it "Produces church numerals when redued" $ do
      (reduce $ reduce $ reduce snum1) `shouldBe` num2
      reduceFully snum2 `shouldBe` num3
      reduceFully (Pair successor num0) `shouldBe` num1

    it "Unreduced successor expressions are not equivalent to numerals" $ do
      Pair successor num0 `shouldNotBe` num1

  describe "Principal form" $ do
    it "Reductions often break equivalence due to variable renaming" $ do
      reduceFully (Pair (Pair add num1) num2) `shouldNotBe` num3
    it "Principal form harmonizes variable names to their \"natural order\"" $ do
      (principalForm $ reduceFully (Pair (Pair add num1) num2))
        `shouldBe` principalForm num3        
      (varsFromBinders $ principalForm (Pair (Pair add_church33 num2) num2))
        `shouldBe` [var "a" .. var "i"]
        
    it "Principal form of a pair of lambdas make bound variables unique" $ do
      (getVars $ principalForm $ Pair (Lambda vx _x) (Lambda vy _y))
        `shouldBe` [var "a", var "b"]
        
    it "Principal form of 𝝺xy . y(x) should be 𝝺ab . b(a)" $ do 
      (principalForm $ Lambda vx (Lambda vy (Pair _y _x)))
        `shouldBe` Lambda va (Lambda vb (Pair _b _a))
        
    it "Principal form of 𝝺x . x(𝝺z . b(z)) should be 𝝺a . a(𝝺c . b(c))" $ do
      (principalForm $ Lambda vx (Pair _x (Lambda vz (Pair _b _z))))
        `shouldBe` Lambda va (Pair _a (Lambda vc (Pair _b _c)))
        
    it "Principal form  of 𝝺ba . b(a) should be 𝝺ab . a(b)" $ do
      (principalForm (Lambda vb (Lambda va (Pair _b _a))))
        `shouldBe` (Lambda va (Lambda vb (Pair _a _b)))
       
    it "Principal form of 𝝺cab . a(c(a,b)) should be 𝝺abc . b(a(b,c))" $ do
      (principalForm successor) `shouldBe`
        Lambda va (Lambda vb (Lambda vc (Pair _b (Pair (Pair _a _b) _c))))
     
  describe "Principal Normal Form is examplified in Church 36 as follows" $ do
    it ("\"The formulas " ++ (show exp_rosser35)
        ++ " and 𝝺a . a(𝝺c . b(c)) are in principal normal form") $ do
      isPrincipalNormalForm exp_rosser35
        && isPrincipalNormalForm (Lambda va (Pair _a (Lambda vc (Pair _b _c))))
        `shouldBe` True
    it "and 𝝺ac . c(a), "$ do
      let f = Lambda va (Lambda vc (Pair _a _c))
        in
        isNormalForm f && not (isPrincipalNormalForm f) `shouldBe` True
    it "and 𝝺bc . c(b), " $ do
      let f = Lambda vb (Lambda vc (Pair _b _c))
        in isNormalForm f && not (isPrincipalNormalForm f) `shouldBe` True

    it ("and 𝝺a . a(𝝺a . b(a)) "
        ++ "are in normal form but not in principal normal form\"") $ do
      let f = Lambda va (Pair _a (Lambda va (Pair _b _a)))
        in isNormalForm f && not (isPrincipalNormalForm f) `shouldBe` True
  
  describe "Addition" $ do
      describe "Church defined addition in terms of successor and it works" $ do
        it "2 + 2 = 4" $ do
          (principalForm $ reduceFully (Pair (Pair add_church33 num2) num2))
            `shouldBe` principalForm num4
        it "4 + 4 = 8" $ do
          (principalForm $ reduceFully
            (Pair (Pair add_church33 $ toNumeral 4) (toNumeral 4)))
            `shouldBe` (principalForm $ toNumeral 8)
      it "17 + 23 = 40" $ do
        (principalForm $ reduceFully
         (Pair (Pair add_church33 $ toNumeral 17) (toNumeral 23)))
          `shouldBe` (principalForm $ toNumeral 40)

      describe "Rosser defined addition directly and that also works" $ do
        it "2 + 2 = 4" $ do
          (principalForm $ reduceFully (Pair (Pair add_rosser35 num2) num2))
            `shouldBe` principalForm num4
        it "4 + 4 = 8" $ do
          (principalForm $ reduceFully
            (Pair (Pair add_rosser35 $ toNumeral 4) (toNumeral 4)))
            `shouldBe` (principalForm $ toNumeral 8)
      it "17 + 23 = 40" $ do
        (principalForm $ reduceFully
         (Pair (Pair add_rosser35 $ toNumeral 17) (toNumeral 23)))
          `shouldBe` (principalForm $ toNumeral 40)

      it "The two implementations are not equivalent" $ do
        (principalForm $ reduceFully add_rosser35)
          `shouldNotBe` (principalForm $ reduceFully add_church33)
      

  describe "Multiplication" $ do
      describe "Church's definition relied on subtraction (Church 33)" $ do
        it "which relied on the iota operator, later found inconsistent" $ do
          False `shouldBe` False
      describe "Rosser's definition in Kleene 35 is direct and it works" $ do
        it "2 * 2 = 4" $ do
          (principalForm $ reduceFully (Pair (Pair mul_rosser35 num2) num2))
            `shouldBe` principalForm num4
        it "4 * 4 = 16" $ do
          (principalForm $ reduceFully
            (Pair (Pair mul_rosser35 $ toNumeral 4) (toNumeral 4)))
            `shouldBe` (principalForm $ toNumeral 16)
        it "17 * 23 = 391" $ do
          (principalForm $ reduceFully
           (Pair (Pair mul_rosser35 $ toNumeral 17) (toNumeral 23)))
            `shouldBe` (principalForm $ toNumeral 391)

      
  describe ("Exponentiation, not defined in Church 32-36, but in Kleene 35 as "
            ++ show exp_rosser35) $ do
    describe "Kleene 35 attributes this formulation to J.B. Rosser and it works" $ do
      it "2 ^ 2 = 4 with principal form applied frist" $ do
        (principalForm $ reduceFully $ principalForm (Pair (Pair exp_rosser35 num2) num2))
          `shouldBe` principalForm num4          
      it "2 ^ 2 = 4 without principal form applied first" $ do
        (principalForm $ reduceFully (Pair (Pair exp_rosser35 num2) num2))
          `shouldBe` principalForm num4
      it "4 ^ 4 = 256" $ do
        (fromNumeral $ reduceFully $ principalForm $
          app exp_rosser35 [toNumeral 4, toNumeral 4])
          `shouldBe` 256
          
      it "7 ^ 5 = 16807" $ do
        (fromNumeral $ reduceFully $ principalForm
          (Pair (Pair exp_rosser35 $ toNumeral 7) (toNumeral 5)))
          `shouldBe` 16807


testmain :: IO ()
testmain = hspec spec

tm = testmain
main = tm
