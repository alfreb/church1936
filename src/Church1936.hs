{-| A
/ "The notion of  𝝺-dfinability is due jointly to the present author and        /
/ S.C. Kleene, successive steps towards it having been taken by the present     /
/ author in the Annals of Mathematics, vol. 34 (1933), p. 863, and by Kleene in /
/ the American Journal of Mathematics, vol. 57 (1935), p. 219"                  /

Alonzo Church, in "An Unsolvable Problem of Elementary Number Theory",
American Journal of Mathematics, vol. 58 (1936), p. 345

This projects implements lambda calculus as it appeared in that paper, down to
the shape of each breacket. It also provides implementations of addition and
multiplication by J.B. Rosser, published in previous papers, directly cited by
Church in the above quote.

== References:

- __Church 36:__ The surviving parts of lambda calculus, after at least two inconsistencies were found.

    - Church, Alonzo. “An Unsolvable Problem of Elementary Number Theory.” American Journal of Mathematics, vol. 58, no. 2, 1936, pp. 345–63. JSTOR, https://doi.org/10.2307/2371045. Accessed 22 Jan. 2023.

- __Church-Rosser 36:__ Contains proofs of the two non-trivial theorems listed on Church 36 p.348. Also provides some more intuition to the three operations on formulas called "Church's Rules I, II, III" in it, and introduces the names /reduction/ for operation II and /expansion/ for operation III. 

    - Church, Alonzo, and J. B. Rosser. “Some Properties of Conversion.” Transactions of the American Mathematical Society, vol. 39, no. 3, 1936, pp. 472–82. JSTOR, https://doi.org/10.2307/1989762. Accessed 20 Feb. 2023.

- __Kleene 35:__ The two part paper proving that all recursive functions are lambda-definable. Lambda arithmetic is found in Part I, while Church references Part II, where the main result is found; that all recursive functions are 𝝺-definable.

    - Kleene, S. C. “A Theory of Positive Integers in Formal Logic. Part I.” American Journal of Mathematics, vol. 57, no. 1, 1935, pp. 153–73. JSTOR, https://doi.org/10.2307/2372027. Accessed 22 Jan. 2023.

    - Kleene, S. C. “A Theory of Positive Integers in Formal Logic. Part II.” American Journal of Mathematics, vol. 57, no. 2, 1935, pp. 219–44. JSTOR, https://doi.org/10.2307/2371199. Accessed 22 Jan. 2023.

- __Church 33:__ A revised version of the original, where inconsistencies relating to Richard's Paradox were amended.

    - Church, Alonzo. “A Set of Postulates For the Foundation of Logic.” Annals of Mathematics, vol. 34, no. 4, 1933, pp. 839–64. JSTOR, https://doi.org/10.2307/1968702. Accessed 22 Jan. 2023.

- __Church 32:__ The first appearance of lambda calculus. Originally a part of a larger project to provide a foundation for all of mathematics.

    - Church, Alonzo. “A Set of Postulates for the Foundation of Logic.” Annals of Mathematics, vol. 33, no. 2, 1932, pp. 346–66. JSTOR, https://doi.org/10.2307/1968337. Accessed 22 Jan. 2023.

-}
module Church1936 (
  symbols, Variable, isVariableStr, var,
  toSubscriptVar, 
  Formula (Var, Pair, Lambda),toVar, isWellFormed,
  isFree, isBound, boundVars, freeVars, getVars, varsFromBinders,
  abbreviate, Toggle (ON, OFF),
  num1, num2, num3, 
  operation_I, operation_II, operation_III,
  replace, reduce, expand,
  toNumeral, fromNumeral,
  app,
  reduceN, reduceFully, reduceAllowed,
  harmonize, principalForm, isPrincipalForm, isPrincipalNormalForm,
  isNormalForm, 
  successor, add, mul, add_church33, add_rosser35, mul_rosser35,
  exp_rosser35, expn,
  ) where

import qualified Data.Char as Char
import qualified Test.QuickCheck as QuickCheck
import Data.List
import qualified Data.Map as Map
import Control.Monad
import Data.Either

{-| The list of valid symbols in a formula. 
/ "We select a particular list of symbols, consisting of the symbols           /
/ { ,), ( ,), 𝝺, [ ,]"                                                         /

Church 36, p.346

These same symbols appeard in the longer list of "undefined terms" in Church 32.
-}
symbols  = "{}()𝝺,[]"
isSymbol = (`elem` symbols)


{-| 

/ "[...] an enumerably infinite set of symbols a, b, c, ...                 /
/ to be called variables."                                                       /
Church 36, p.346

Indexing variables using subscript is implicitly accepted as well:

/ "A formula 𝝺x₁,[𝝺x₂,[. ..𝝺xn,[M] ...]] may be abbreviated as 𝝺x₁,x₁,. . .xn"  /
Church 36, p.347

In order to preserve the convention for variables, the type constructor is not
exported. Instead use 'var'.
-}
newtype Variable = V String -- Should be just Char? we need a lot though
  deriving Eq

instance Show Variable where
  show (V s) = s


alphabet  = take 26 ['a'..] ++ take 26 ['A'..]
subdigits = take 10 ['₀'..]

isSubdigit x   = x `elem` subdigits

isIndex []     = False
isIndex (x:xs) = isSubdigit x
                 && x /= '₀'
                 && (and $ map isSubdigit xs)

-- | Predicate to validate if a string follows Church's convention for variable
-- notation.
isVariableStr :: String -> Bool
isVariableStr [x]    = x `elem` alphabet
isVariableStr (x:xs) = x `elem` alphabet
                    && isIndex xs

subscriptDigits = "₀₁₂₃₄₅₆₇₈₉"

-- | Variable type constructor, ensuring notation conventions
var :: String -> Variable
var s = V (if isVariableStr s
                   then s
                   else error "Invalid variable format")

-- | Predicate to validate a variable
isVariable :: Variable -> Bool
isVariable (V s) = isVariableStr s


{-|
/ "A variable x standing alone is a well-formed formula                         /
/and the occurrence of x in it is an occurrence of x as a free variable in it;" /
/ if the formula M is well-formed and contains an occurrence of x as a free    /
/ variable in M, then 𝝺x[M] is well-formed"                                     /

Church 36 p. 346

__Note:__ The requirement that x must occur free in M for 𝝺x[M] to be well-formed can only
be fulfilled at runtime. Use 'isWellFormed' to validate this requirement.
-}
data Formula = Var Variable |
               Pair Formula Formula |
               Lambda Variable Formula
  deriving Eq


-- Alternative type:
data AltFormula = L String [AltFormula] | V' String
  deriving (Eq, Show)

wellFormedAlt :: [AltFormula] -> Bool
wellFormedAlt [V' s]   = True
wellFormedAlt [L v f] = wellFormedAlt f
wellFormedAlt (f:fs)  = wellFormedAlt [f] && wellFormedAlt fs

f1_alt = [V' "a"]
f2_alt = [L "x" [V' "x"]]



{-| Predicate to determine if a variable is free in a formula.

"if the formulas F and X are well-formed, {F}(X) is well-formed, and an
occurrence of x as a free (bound) variable in F or X is an occurrence of x
as a free (bound) variable in {F} (X)"


"any occurrence of x in 𝝺[M] is an
occurrence of x as a bound variable in 𝝺x[M], and an occurrence of a variable y,
other than x, as a free (bound) variable in M is an occurrence of y as a free
(bound) variable in 𝝺x[M]."

Freeness extends to formula pairs and Lambda x M binds x in M.
-}

isFree v (Var v') = v == v'
isFree v (Pair l r)  = isFree v l || isFree v r
isFree v (Lambda v' f) = v /= v' && isFree v f



flatten (Pair (Var v) f) = [(Var v), f]
flatten (Pair f x) = flatten f ++ [x]
flatten f = [f]

extractLambdas :: ([Variable], Formula) -> ([Variable], Formula)
extractLambdas (vars, (Lambda x f)) = extractLambdas (vars ++ [x], f)
extractLambdas (vars, f) = (vars, f)

-- | Simple feature toggle 
data Toggle = ON | OFF deriving Show
cfg_abbrev = ON

abbreviate :: Toggle -> Formula -> String

{-|

Church's formula abbreviation rules: 

- "A formula {F}(X) may be abbreviated as F(X) in any case where F is or is
represented by a single symbol."

- "A formula {{F}(X)} (Y) may be abbreviated as {F}(X, Y), or, if F is or is
represented by a single symbol, as F(X, Y)."

- "And {{{F}(X)}(Y)}(Z) may be abbreviated as {F}(X, Y, Z), or
as F(X,Y,Z), and so on."

- "A formula 𝝺x1,[𝝺x1,[. ..𝝺xn,[M] ...]] may be abbreviated as 𝝺x1,x2,. . .xn"

The function is implemented with a toggle and used by "Show" for formulas;
- ON (Default) abbreviates according to the rules
- OFF makes no abbreviations and provides the full, original syntax

-}

abbreviate ON (Var (V v)) = v

{-| "A formula {F}(X) may be abbreviated as F(X) in any casewhere F is or is
represented by a single symbol." -}
abbreviate ON  (Pair (Var (V f)) x) = "" ++ f ++ "(" ++ abbr ON x ++ ")"

{-| "A formula {{F}(X)} (Y) may be abbreviated as {F}(X, Y), or, if F is or is
represented by a single symbol, as F(X, Y)." -}
abbreviate ON  (Pair (Pair (Var (V f)) x) y)  = f ++ "("
  ++ abbr ON x ++ "," ++ abbr ON y ++ ")"

{-| "And {{{F}(X)}(Y)}(Z) may be abbreviated as {F}(X, Y, Z), or
as F(X,Y,Z), and so on." -}
abbreviate ON  (Pair f1 f2) = let (f:xs) = flatten f1 in
  showList f (showTail xs)
  where
    showList (Var (V v)) rest = v ++ rest
    showList f rest = "{" ++ abbr ON f ++ "}" ++ rest
    showTail [] = "(" ++ abbr ON f2 ++ ")"
    showTail xs = "(" ++ (tail (init (show xs))) ++ "," ++ abbr ON f2 ++ ")"

{-| "A formula 𝝺x1,[𝝺x1,[. ..𝝺xn,[M] ...]] may be abbreviated as 𝝺x1,x2,. . .xn"
-}
abbreviate ON (Lambda v f)  = let (xs, f') = extractLambdas ([v], f) in
  "𝝺" ++ showVars xs ++ " . " ++ abbr ON f' ++ ""
  where showVars [] = ""
        showVars ((V v):vs) = v ++ showVars vs

abbreviate OFF (Var (V v)) = v
abbreviate OFF (Pair f1 f2) = "{" ++ abbr OFF f1 ++ "}(" ++ abbr OFF f2 ++ ")"
abbreviate OFF (Lambda (V v) f) = "𝝺" ++ v ++ "[" ++ abbr OFF f ++ "]"


abbr = abbreviate


instance Show Formula where
  show (Var (V v))  = v
  show f = abbreviate cfg_abbrev f


{-| Convenience function. Create a Formula variable from a string, ensuring correct syntax.

Equivalent to 'Var' '.' 'var' 
-}
toVar = Var . var

-- Helper variables 
va = var "a"
vb = var "b"
vc = var "c"
vd = var "d"
vx = var "x"
vy = var "y"
vf = var "f"
vi = var "i"
vk = var "k"
vm = var "m"
vn = var "n"
vz = var "z"


_a = toVar "a"
_b = toVar "b"
_c = toVar "c"
_d = toVar "d"
_m = toVar "m"
_n = toVar "n"
_o = toVar "o"
_p = toVar "p"
_f = toVar "f"
_x = toVar "x"
_y = toVar "y"
_z = toVar "z"



{-|

"We introduce at once the following infinite list of abbreviations,

                        1 → 𝝺ab . a(b),

                        2 → 𝝺ab . a(a(b))

                        3 → 𝝺ab . a(a(a(b)),

and so on, each positive integer in Arabic notation standing for a formula of
the form 𝝺ab . a(a( ... a(b) ... ))."

-}
num1 = Lambda va (Lambda vb (Pair _a _b))

-- | 2 → 𝝺ab . a(a(b))
num2 = Lambda va (Lambda vb (Pair _a (Pair _a _b)))

-- | 3 → 𝝺ab . a(a(a(b))
num3 = Lambda va (Lambda vb (Pair _a (Pair _a (Pair _a _b))))


-- Helpers for from / to numerals

toNumeralPair 1 = Pair (toVar "a") (toVar "b")
toNumeralPair n = Pair (toVar "a") (toNumeralPair (n-1))

fromNumeralPair (Pair (Var a) (Var b)) = 1
fromNumeralPair (Pair (Var a) p) = 1 + (fromNumeralPair p)

-- | Generate Church numeral from a numeric value
toNumeral n = Lambda va (Lambda vb (toNumeralPair n))

-- | Generate numeric value from Church numeral
fromNumeral (Lambda va (Lambda vb (p))) = fromNumeralPair p

prop_numerals_valid (QuickCheck.Positive n) = fromNumeral(toNumeral n) == n

-- We can now fulfill Enum class constraints for Church numerals
instance Enum Formula where
  toEnum   e = toNumeral e
  fromEnum n = fromNumeral n


{-| "We consider the three following operations on well-formed formulas:

I. To replace any part 𝝺x[M] of a formula by 𝝺y[S(x,y)M|], where y is a
variable which does not occur in M."

Church 36 p.347

Note: We've adopted syntax S(x,y) where Church placed x on top of y without
the use of parenthesis.



"


-}
operation_I   :: Variable -> Variable -> Formula -> Formula


{-| "II. To replace any part {𝝺x[M]}(N) of a formula by S(x,N)M|, provided that
the bound variables in M are distinct both from x and from the free variables
in N."

Church 36 p.347

"A conversion which contains exactly one application of Operation II,and no
application of Operation III,is called a reduction."

Church 36 p.348

Operation II is also called /reduction/ in "Some properties of conversion",
Church-Rosser 36.

-}
operation_II  :: Formula -> Formula
operation_II (Pair (Lambda x m) n) =
  if boundVars m `distinctFrom` (x : freeVars n)
  then replaceN x n m
  else (Pair (Lambda x m) n)
  

{-|
"
III. To replace any part S(x,N)M| I (not immediately following 𝝺) of a formula
by {𝝺x[M]}(N), provided that the bound variables in M are distinct both from x
and from the free variables in N.
"

Church 36 p.347

Operation III is Called /Expansion/ in "Some properties of conversion",
Church-Rosser 36.
-}
operation_III :: Formula -> Formula -> Formula
operation_III n m = let x = fresh n m in
                      (Pair (Lambda x (replaceX x n m)) n)

replaceV :: Variable -> Variable -> Formula -> Formula
replaceV x y (Var v) = if v == x then (Var y) else (Var v)
replaceV x y (Pair a b) = (Pair (replaceV x y a) (replaceV x y b))
replaceV x y (Lambda v f)  = if x /= v then (Lambda v (replaceV x y f))
                             else (Lambda y (replaceV x y f))

replaceN :: Variable -> Formula -> Formula -> Formula
replaceN x n (Var v) = if x == v then n else (Var v)
replaceN x n (Pair a b) = Pair (replaceN x n a) (replaceN x n b)
replaceN x n (Lambda y f) = if x == y then (Lambda y f) -- illegal, x bound twice
                           else (Lambda y (replaceN x n f))

replaceX :: Variable -> Formula -> Formula -> Formula
replaceX x n (Var v) = if (Var v) == n then (Var x) else (Var v)
replaceX x n (Pair a b) = Pair (replaceX x n a) (replaceX x n b)
replaceX x n (Lambda y f) = if x == y then (Lambda y f) -- illegal, x bound twice
                          else (Lambda y (replaceX x n f))

fresh a b  = freshVar $ nub (getVars a ++ getVars b)
               

operation_I   =  replaceV

substitute = operation_I


-- Here a reduction takes into account all bound variables of the parent scope
-- Leftmost first, innermost first

reduceWithVarRewrite :: [Variable] -> Formula -> Formula
reduceWithVarRewrite b (Pair (Lambda x m) n) =
  let f = (Pair (Lambda x m) n)
      m' = reduceWithVarRewrite (x : b) m
  in
    if m /= m' 
    then Pair (Lambda x m') n
    else let n' = reduceWithVarRewrite (x : b) n in
           if n' /= n 
           then Pair (Lambda x m') n'           
           else let boundm = [ x | x <- b, x `elem` (getVars m)]
                    m' = m `distinguishBoundFrom` ((x : freeVars n) ++ boundm)
                in
                  operation_II (Pair (Lambda x m') n')
    
reduceWithVarRewrite b (Var x) = (Var x)
reduceWithVarRewrite b (Lambda x f) = (Lambda x (reduceWithVarRewrite (x : b) f))
reduceWithVarRewrite b (Pair x y) = let x' = reduceWithVarRewrite b x in
                            if x' == x then (Pair x (reduceWithVarRewrite b y)) -- Leftmost first
                            else (Pair x' y)


-- Naive reduction without taking the variable rules into account
reduceNaive (Pair (Lambda x m) n) = operation_II (Pair (Lambda x m) n)
reduceNaive (Var x) = (Var x)
reduceNaive (Lambda x f) = (Lambda x (reduceNaive f))
reduceNaive (Pair x y) =
  let x' = reduceNaive x in
    if x' == x
    then (Pair x (reduceNaive y)) -- Leftmost first
    else (Pair x' y)


data ReductionToggle = Clever | Naive

redux Clever f = reduceWithVarRewrite [] f
redux Naive f = reduceNaive f

reduce = redux Clever

reduceN n f = let f' = reduce f in
               if f' == f || (n <= 0) then f
               else reduceN (n-1) f'

maxSteps = 1000

reduceFully f = reduceN maxSteps f

expand     = operation_III

lambda x f = Lambda (V x) f

𝞴 = lambda

app x l = foldl Pair x l

num1'  = (𝞴 "x" (𝞴 "y" (Pair _x _y)))
num2' = (𝞴 "x" (𝞴 "y" (app _x [_x, _y])))

-- add' x y =  app add [x, y]

add_church33' = (𝞴 "x" (𝞴 "y" (app _y [successor, _x])))
add_rosser35' = (𝞴 "x" (𝞴 "y" (𝞴 "a" (𝞴 "b" (app _x [_a, app _y [_a, _b]])))))


-- apply (Lambda x m) n  = reduce (Pair (Lambda x m) n)

-- Pair: Short for pair
--Pair (Var a) b = Pair (Var a) b
--Pair (Lambda v f) p = Pair (Lambda v f) p
--Pair (Pair a b) c = Pair (Pair a b) c


successor = Lambda vc (Lambda va (Lambda vb (Pair _a (Pair (Pair (Var vc) _a) _b))))




{-
Kleene 35, crediting Rosser:
"A Theory of Positive Integers in Formal Logic" (Jan.'35, first received '33, revised '34)
https://www.jstor.org/stable/2372027

" We follow Church in these definitions, but not in the definition of addition,
because J.B. Rosser has proposed one which leads to simpler formal proofs",
p.156


1 → 𝝺fx.f(x)
S → 𝝺𝝆fx.f(𝝆(f,x))         
N → 𝝺𝝁.[𝜙(1).𝜙(x) ] ...
2→S(1), 3→S(2), 4→S(3),... -- Equivalent to Church '36


And then

+ → 𝝺𝝆𝝈fx.𝝆(f(𝝈(f,x)))  

"... due to J.B. Rosser, and abbreviate ...".


We need Church '33, the revised version of the '32 paper, to get the integer operations
- https://www.jstor.org/stable/1968702

-}

-- | Addition according to Church 1933.
--
-- / "The equivalent of the recursion formulas, m + 1 = S(m), and /
-- / m + (k + 1) = S(m + k), is, in fact, obtained by defining:   /
--
-- / + → 𝝺m𝝺n . n(S,m).                                           /
-- 
-- 
-- Church 33 p.863
add_church33 = Lambda vm (Lambda vn (Pair (Pair _n successor) _m))



-- | Addition according to Kleene 1935, attributed to J.B. Rosser.
-- 
-- / "We follow Church in these definitions, but not in the definition of       /
-- / addition, because J.B. Rosser has proposed one which leads to simpler      /
-- / formal proofs"                                                             /
--
-- p.156
-- 
-- /"5. Addition. We adopt the definition                                       /
--
-- / + → 𝝺𝝆𝝈fx.𝝆(f,𝝈(f,x)),                                                     /
--
-- / due to J.B. Rosser, and  abbreviate {+}(x,y) to [x] + [y]."                /
--
-- p.160
--
-- Rosser's definition is direct, avoiing the use of successor. 
-- From Kleene 35, pp.156-160
add_rosser35 = Lambda (V "p")
               (Lambda (V "o")
                (Lambda (V "f")
                 (Lambda (V "x") (Pair (Pair _p _f) (Pair (Pair _o _f) _x)))))


-- add = Lambda (V "m") (Lambda (V "n") (Pair _m (Pair successor _n)))
add = add_rosser35


-- | Multiplication according to Kleene 1935, attributed to J.B. Rosser.

mul_rosser35 = Lambda (V "a")
               (Lambda (V "b")
                (Lambda (V "x")(Pair _a (Pair _b _x))))

exp_rosser35 = Lambda (V "a") (Lambda (V "b") (Pair _b _a))

mul  = mul_rosser35
expn = exp_rosser35

replace = operation_I


getFvars :: Formula -> [Formula]

getFvars (Var v) = [Var v]
getFvars (Pair a b) = nub (getFvars a ++ getFvars b)
getFvars (Lambda v f) = getFvars f

getBoundVars :: Formula -> [Variable] -> [Variable] -> [Variable]
getBoundVars (Var v) bound vars = if (elem v bound) && not (elem v vars)
                                 then vars ++ [v]
                                 else vars
                                      
getBoundVars (Pair x y) b vs = nub (getBoundVars x b vs ++ getBoundVars y b vs)
getBoundVars (Lambda v f) b vs = getBoundVars f (b ++ [v]) vs


-- | Get all free variables in a formula, in the order they are used
freeVars :: Formula -> [Variable]
freeVars (Var v)       = [v]
freeVars (Pair l r)  = freeVars l ++ freeVars r
freeVars (Lambda v f) = filter (/= v) (freeVars f)

-- | Get all bound variables in a formula, in the order they are used
boundVars :: Formula -> [Variable]
boundVars f  = getBoundVars f [] []

-- | Predicate to determine if a given variable is bound in a given formula
isBound x f = x `elem` boundVars f


-- Var rewriting according to Turing '37 (Dec. 1937)

{-
"In this section the notion of 𝞴-𝐾-definability is introduced in a form suitable
for handling with machines. There will be three differences to the normal, in
addition to that whihch distinguishes 𝞴-𝐾-definability from 𝞴-definability. One
consists in using only one kind [] of bracket instead of three, {}()[]; another
is that x, x¹,x¹¹,... are used as variables instead of an indefinitie infinite
list of the single symbos, and the third is a change in the form of condition
(ii) of immediate transformability not affecting the definition of
convertibility except in form."
-}

-- I'm adopting this convention, but using subscript instead of prefix and
-- decimal notation instead of unary numbers

-- Church already uses this convention implicitly in Church36 p.347:
{- "A formula 𝝺x1,[𝝺x1,[. ..𝝺xn,[M] ...]] may be abbreviated as 𝝺x1,x2,. . .xn"s
-}

decStrToSubscript []     = []
decStrToSubscript (x:xs) =
  if not (Char.isDigit x) then []
  else (subscriptDigits !! ((Char.ord x)
                             - Char.ord('0')):decStrToSubscript(xs))

toSubscript    n = decStrToSubscript $ show n 

-- | Construct a Variable with subscript notation, e.g. x₁, b₂, y₉₉.
-- 
-- Church uses subscript to enumerate variables. Church 36 p.347.
toSubscriptVar x n = var ([x] ++ toSubscript n)
toSubscriptVarx = toSubscriptVar 'x'

intFromSubscript []     = 0
intFromSubscript [x]    = (Char.ord x) - (Char.ord '₀')
intFromSubscript (x:xs) = 10^(length xs) * ((Char.ord x) - (Char.ord '₀'))
                                + intFromSubscript xs



{-| "A variable x standing alone is a well-formed formula and
the occurrence of x in it is an occurrence of x as a free variable in it"

...

"if the formula M is well-formed and contains an occurrence of x as a free
variable in M, then 𝞴x[M] is well-formed"

Church 36 p.346


-}
isWellFormed (Var v) = True
isWellFormed (Pair l r) = isWellFormed l && isWellFormed r

-- if the formula M is well-formed and contains an occurrence of x as a free
-- variable in M, then 𝞴x[M] is well-formed
isWellFormed (Lambda v f) = isFree v f && isWellFormed f


isNormalForm (Var v)                 = True
isNormalForm (Pair (Lambda v l) r) = False
isNormalForm (Pair l r)  = isNormalForm l && isNormalForm r
isNormalForm (Lambda v f) = isNormalForm f




distinctFrom l1 l2 = and (map (\x -> not (elem x l2)) l1)

distinct vars = [x | x <- [var "a" ..], not (x `elem` vars)]
firstDistinct vars = head $ distinct vars

reduceAllowed (Var v)       = True
reduceAllowed (Lambda v f) = reduceAllowed f
reduceAllowed (Pair (Lambda x m) n) =
  boundVars m `distinctFrom` (x : freeVars n)
reduceAllowed (Pair l r) = reduceAllowed l && reduceAllowed r


instance Enum Variable where
  fromEnum (V (v:vs)) = 26 * (intFromSubscript vs) + (Char.ord v - Char.ord 'a')
  toEnum n = let (m,r) = divMod n 26 
                 char  = Char.chr ((Char.ord 'a') + r)
             in if m > 0
                then toSubscriptVar char m
                else var [char]
                 
instance Ord Variable where
  compare v  v' = compare (fromEnum v) (fromEnum v')
    


maxVar vars = foldl max (V "`") vars
maxFvar vars = maxVar $ map (\(Var v) -> v) vars



-- | Get a list of all variables in a formula, in the order they are used.
getVars f = map (\(Var v) -> v) (getFvars f)
                               
enumerateVars f = zip (getVars f) [1..]
toUniformSubscriptVars f = map (\(v,i) -> (v, toSubscriptVarx i))
                           $ enumerateVars  f

  
getVarsFromBinders vs (Var v)      = []
getVarsFromBinders vs (Pair l r)   =  getVarsFromBinders vs l
                                      ++ getVarsFromBinders vs r
getVarsFromBinders vs (Lambda v f) = vs ++ [v] ++ getVarsFromBinders vs f

-- | Get a list of all variables directly following a 𝝺, in order of appearance.
varsFromBinders = getVarsFromBinders []



-- make sure all lambdas in a formula bind a unique var
harmonizef bound (Var v) = (Var v)                                
harmonizef bound (Lambda x f) = let x' = firstDistinct bound 
                                    f' = operation_I x x' f
                                in Lambda x' (harmonizef (x':bound) f')

harmonizef bound (Pair a b) = let a' = harmonizef bound a
                                  bound' = (getVars a' ++ bound)
                              in Pair a' (harmonizef bound' b)
                                   

harmonize f = harmonizef (getVars f) f


distinguishBoundFrom f vars = let (V (v:vs)) = maxVar vars in
                                if (varsFromBinders f) `distinctFrom`  vars
                                then f
                                -- else harmonizeBound f v ((intFromSubscript vs) + 1)
                                else harmonizef (getVars f) f -- we may have outer binders for some of the vars

testVars = [toSubscriptVar 'x' 5, toSubscriptVar 'x' 3,
            var "a", toSubscriptVar 'y' 5]

freshVar vs = succ (maxVar vs)


  
prop_dontReduceToNotWellFormed =
  not (reduceAllowed (Pair num1 _b)) 
  && isWellFormed (reduce (Pair num1 _b))
  && isWellFormed (Pair num2 num2)
  && isWellFormed (reduce $ (Pair num2 num2))


doubleBinding1 = Lambda (V "a")
                 (Lambda (V "a") (Pair _a _a))

prop_doubleBindingsIllFormed = not $ isWellFormed doubleBinding1

doubleBinding2 = Lambda (V "a")
                 (Pair (Lambda (V "a") _a) _b)

doubleBinding3 = Lambda (V "a")
                 (Pair (Lambda (V "b") _a) _b)


trickyBinding = reduce (Pair num1 num1)



maxVar :: Foldable t => t Variable -> Variable


{-| a formula is said to be in principal normal form if it is in normal form, and no variable occurs in it both as a free variable and as a bound variable, and the variables which occur in it immediately following the symbol h are, when taken in the order in which they occur in the formula, in natural order without repetitions, beginning with a and omitting only such variables as occur in the formula as free variable".
-}  
principalForm f = harmonizef (freeVars f) (harmonize f)

isPrincipalForm f = principalForm f == f

isPrincipalNormalForm f = isPrincipalForm f && isNormalForm f

reduceMb :: Formula -> IO (Maybe Formula)
reduceMb (Var v) = do liftM return Just (Var v)
reduceMb (Lambda v f) = do
  x <- reduceMb f
  if x == Nothing
    then
    do
      putStrLn ("Couldn't reduce " ++ show (f))
      return Nothing
    else return x
    


data ErrReduce =
  ErrFree Formula Formula Formula [Variable] |
  ErrVar Formula Formula Variable
  deriving (Show, Eq)

reducibleM :: Formula -> (Either ErrReduce Formula)

reducibleM (Var v) = Right (Var v)

reducibleM (Lambda v f) = do
  f' <- reducibleM f
  return (Lambda v f')

reducibleM (Pair (Lambda x m) n) =
  let f = (Pair (Lambda x m) n) in 
    if not (boundVars m `distinctFrom` [x])
    then Left (ErrVar f m x)
    else
      if not (boundVars m `distinctFrom` freeVars n)
      then Left (ErrFree f m n (freeVars n))
      else Right f



reducibleM (Pair l r) = do
  l' <- reducibleM l
  r' <- reducibleM r
  return (Pair l' r')


-- Convert a failed reduction to string, forward success

explanation :: (Either ErrReduce Formula) ->
  (Either String Formula)

explanation (Right f)   = Right f
explanation (Left (ErrVar f m v)) =
  Left ("Could not reduce \n" ++ (show f) ++ "\nbecause "
         ++ "the bound variables in \n" ++ (show m)
         ++ "\nare not distinct from binder variable "
         ++ (show v))

explanation (Left (ErrFree f m n vs)) =
  Left ("Could not reduce \n" ++ (show f) ++ "\nbecause "
         ++ "The bound variables in \n" ++ (show m)
         ++ "\nare not distinct from the free vars in\n"
         ++ (show n) ++ " which are "
         ++ (show vs))

  
reductionOrExplanation f = do
  r  <- explanation (reducibleM f)
  r' <- explanation (reducibleM $ reduce r)
  if isNormalForm r' || r == r'
    then return r'
    else reductionOrExplanation r'


toIO :: (Either String Formula) -> IO ()
toIO (Right f) = putStrLn (show f)
toIO (Left s)  = putStrLn s
  

reduceOrExplain = toIO . reductionOrExplanation

reducible f = isRight $ reducibleM f

f = Lambda vx (Pair _x (Lambda vz (Pair _b _z)))
f' = app (reduceFully $ app exp_rosser35 [num1]) [num1]
tm = do 
  putStrLn $ show $ f
  putStrLn $ show $ reduceN 1 f



-- =============================================================================
--                            Haskell Numerals
-- =============================================================================

recurse f 0 x = x
recurse f n x = f (recurse f (n-1) x)

numeralH n = \x y -> recurse x n y


-- Exponentiation due to Rosser, according to Kleene '35 pt2
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

-- =============================================================================
--                            END Haskell Numerals
-- =============================================================================
