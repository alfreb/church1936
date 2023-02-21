module Main where

import qualified Church1936 as C36

import Data.List

main :: IO ()
main = do
  putStrLn "\nA TL;DR of Church's paper.\n"
  putStrLn "First the symbols of the lanugage of lambda calculus are introduced:"
  putStrLn C36.symbols

  putStrLn "\nThen the variables are introduced as a, b, c ... and so on. We're"
  putStrLn "told that this is an enumerably infinite set of symbols, but he"
  putStrLn "really only provides the first 3, so we have to improvise beyond z."
  putStrLn "We did this by implementing Enum for variables as follows:"
  putStrLn $ (intercalate ", ") $ map show (take 10 [C36.var "x"..])
  putStrLn "... and then"
  putStrLn $ (intercalate ", ") $ map show (take 10 [C36.var "x₁"..])

  putStrLn "\nAny sequence of symbols defined above is a _formula_ in the paper"
  putStrLn "so technically `}(` and `{o₁[` are formulas, but only the"
  putStrLn "well-formed ones are interesting, which Church defines by induction"
  putStrLn "together with _free_ and _bound_ variables.\n"

  
  putStrLn "\"A variable *x* standing alone is a well-formed formula "
  putStrLn "and the occurence of *x* in it is an occurence of *x* as a free"
  putStrLn "variable in it\""

  putStr "\nLet's verify. x is a well formed formula: "
  putStrLn $ show $ C36.isWellFormed $ (C36.Var . C36.var) "x"
  putStr "The `Variable` `x` is free in the `Formula` `Var (V \"x\")`: "
  putStrLn $ show $ C36.isFree (C36.var "x") ((C36.Var . C36.var) "x")


  putStrLn "\nFurther, if the formulas F and X are well-formed, {F}(X) is too."

  let f = C36.toVar "f"
      x = C36.Pair f f
    in
    if C36.isWellFormed $ C36.Pair f x
    then
      putStrLn $ "This is one confirmed example: "
      ++ (C36.abbreviate C36.OFF $ C36.Pair f x)
    else error "Church would not have liked this implementation."

  putStrLn "\nNow for the lambda: if M is well formed and x is free in M, then"
  putStrLn "x is bound in 𝝺x[M]. So 𝝺 has one job: to bind variables."

  let x = C36.toVar "x"
      y = C36.toVar "y"
      m = C36.Pair x (C36.Pair x (C36.Pair x y))
    in
    if C36.isWellFormed m
       && C36.isFree (C36.var "x") m
    then
      putStrLn ("Here's one confirmed example of an M with x as free:\n"
                ++ show m)
    else
      error "Church would not approve of this"
  
  putStrLn "\nAttaching 𝝺x we get a well-formed formula with x now bound:"
  let x = C36.toVar "x"
      y = C36.toVar "y"
      m = C36.Pair x (C36.Pair x (C36.Pair x y))
      m'= C36.Lambda (C36.var "x") m
    in
      if C36.isWellFormed m'
         && C36.isBound (C36.var "x") m'
      then
        putStrLn $ (show m')
      else
        error "Failing this would be a disgrace to lambda calculus"

  
  putStrLn "\nChurch now defines the numerals as follows: "
  putStrLn ("1 → " ++ show C36.num1)
  putStrLn ("2 → " ++ show C36.num2)
  putStrLn ("3 → " ++ show C36.num3)
  
  putStrLn "\nThe successor function is not defined in this paper, but"
  putStrLn "was defined in Church 33 as follows:"
  putStrLn $ show C36.successor

  putStrLn "\nWe can apply the successor function to 2 like so:"
  putStrLn $ show $ C36.Pair C36.successor C36.num2

  putStrLn "\nThe full form of this expression is really this:"
  putStrLn $ C36.abbreviate C36.OFF (C36.Pair C36.successor C36.num2)

  putStrLn "\nThankfully, Church provided a nice set of abbreviation rules to"
  putStrLn "save us from the sea of brackets. You can turn them on or off."
  
  putStrLn "\nApplying Operation II (reduction) repeatedly we eventually get"
  putStrLn "\"normal form\", where no further reduction is possible."
  putStrLn $ show $ C36.reduceN 1 (C36.Pair C36.successor C36.num2) 
  putStrLn $ show $ C36.reduceN 2 (C36.Pair C36.successor C36.num2)
  putStrLn $ show $ C36.reduceN 3 (C36.Pair C36.successor C36.num2)
 
  putStrLn "\nThe successor of 2 is 3. Yay! "
  
  putStrLn "\nAddition can now be implemented in terms of successor:"
  putStrLn $ show $ C36.add_church33

  putStrLn "\nBut for multiplication the plot thickens; Church messed up!"
  putStrLn "(see the documentation for details). Rosser helped fix this, as"
  putStrLn "noted in Kleene 35, with this nice baby:"
  putStrLn $ show $ C36.mul_rosser35

  putStrLn "\nAnd to top it off they point out that the numerals themselves"
  putStrLn "are exponentiation functions. 2(3) is 3^2 and 3(2) = 2^3."
  putStrLn "Reversing the parameters we get it in the order we're used to:"
  putStrLn $ show $ C36.exp_rosser35
  
  putStrLn "\nNotice how this is exactly the same as the number 1, with the"
  putStrLn "variables in reversed order:"
  putStrLn $ show $ C36.num1


  putStrLn "\nLet's end here, with proving that 2 + 2 = 4:"
  putStrLn $ show $ C36.app C36.add [C36.num2, C36.num2]
  putStrLn "\nreduces to "
  putStrLn $ show $ C36.reduceFully $ C36.app C36.add [C36.num2, C36.num2]

  putStrLn "\nPretty neat! Check out the documentation and unit tests for more."
