# church1936
Lambda calculus implemented directly from Alonzo Church's 1936 paper âAn Unsolvable Problem of Elementary Number Theory.â _American Journal of Mathematics_, vol. 58, no. 2, 1936, pp. 345â63. JSTOR, https://doi.org/10.2307/2371045.

[![Haskell CI](https://github.com/alfreb/church1936/actions/workflows/haskell.yml/badge.svg)](https://github.com/alfreb/church1936/actions/workflows/haskell.yml)

Build and run unit tests:
```
$ cabal test
```
Generate the documentation:
```
$ cabal haddock
```
Build and run the example program:
```
$ cabal run church1936
```

The example program prints the following (with some formatting added here for github readability): 

## A TL;DR of Church's paper

First the symbols of the lanugage of lambda calculus are introduced:\
`{}()ðº,[]`\
\
Then the variables are introduced as a, b, c ... and so on. We're
told that this is an enumerably infinite set of symbols, but he
really only provides the first 3, so we have to improvise beyond z.
We did this by implementing Enum for variables as follows: \
`x, y, z, aâ, bâ, câ, dâ, eâ, fâ, gâ`\
... and then \
`xâ, yâ, zâ, aâ, bâ, câ, dâ, eâ, fâ, gâ` \
\
Any sequence of symbols defined above is a _formula_ in the paper
so technically `}(` and `{oâ[` are formulas, but only the
well-formed ones are interesting, which Church defines by induction
together with _free_ and _bound_ variables.  
\
"A variable *x* standing alone is a well-formed formula 
and the occurence of *x* in it is an occurence of *x* as a free
variable in it"\
\
Let's verify. x is a well formed formula: True
The `Variable` `x` is free in the `Formula` `Var (V "x")`: True
\
Further, if the formulas `F` and `X` are well-formed, `{F}(X)` is too.
This is one confirmed example: `{f}({f}(f))`\
\
Now for the lambda: if `M` is well formed and `x` is free in `M`, then
`x` is bound in `ðºx[M]`. So ðº has one job: to bind variables.
Here's one confirmed example of an `M` with `x` as free:\
`x(x(x(y)))`\
\
Attaching ðºx we get a well-formed formula with x now bound:\
`ðºx . x(x(x(y)))`\
\
Church now defines the numerals as follows: 
```
1 â ðºab . a(b)
2 â ðºab . a(a(b))
3 â ðºab . a(a(a(b)))
```
The successor function is not defined in this paper, but
was defined in Church 33 as follows:\
`ðºcab . a(c(a,b))`\
\
We can apply the successor function to 2 like so:\
`{ðºcab . a(c(a,b))}(ðºab . a(a(b)))`\
\
The full form of this expression is really this:\
`{ðºc[ðºa[ðºb[{a}({{c}(a)}(b))]]]}(ðºa[ðºb[{a}({a}(b))]])`\
\
Thankfully, Church provided a nice set of abbreviation rules to
save us from the sea of brackets. You can turn them on or off.
\
Applying Operation II (reduction) repeatedly we eventually get
"normal form", where no further reduction is possible.
```
ðºab . a({ðºab . a(a(b))}(a,b))
ðºab . a({ðºc . a(a(c))}(b))
ðºab . a(a(a(b)))
```
The successor of 2 is 3. Yay!\
\
Addition can now be implemented in terms of successor:\
`ðºmn . n(ðºcab . a(c(a,b)),m)`\
\
But for multiplication the plot thickens; Church messed up!
(see the documentation for details). Rosser helped fix this, as
noted in Kleene 35, with this nice baby:\
`ðºabx . a(b(x))`\
\
And to top it off they point out that the numerals themselves
are exponentiation functions. 2(3) is 3^2 and 3(2) = 2^3.
Reversing the parameters we get it in the order we're used to:\
`ðºab . b(a)`\
\
Notice how this is exactly the same as the number 1, with the
variables in reversed order:\
`ðºab . a(b)`\
\
Let's end here, with proving that 2 + 2 = 4:\
`{ðºpofx . p(f,o(f,x))}(ðºab . a(a(b)),ðºab . a(a(b)))`\
\
reduces to \
`ðºfx . f(f(f(f(x))))`\
\
Pretty neat! 

## The point of the paper
Note that the objective of Church's paper was not to make a computer, it was to prove that GÃ¶del's incompleteness theorem has implications for even simple statements in elementary number theory. More on that later!


