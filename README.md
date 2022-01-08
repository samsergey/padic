# [Math.NumberTheory.Padic][]

 Module introduces p-adic integers and p-adic rational numbers of fixed and arbitratry precision, implementing basic arithmetic as well as some specific functions, i.e. detection of periodicity in digital sequence, rational reconstruction, square roots etc.

 The radix [`p`][] of a p-adic number is specified at a type level via type-literals. In order to use them GHCi should be loaded with '-XDataKinds' extension.

```
> :set -XDataKinds
> 45 :: Z 10
45
> 45 :: Q 5
140.0
```
 Negative p-adic integers and rational p-adics have trailing periodic digit sequences, which are represented in parentheses.

```
> -45 :: Z 7
(6)04
> 1/7 :: Q 10
(285714)3.0
```

The working precision of all p-adics is effetively infinite. However for textual output and rational reconstruction some finite precision should be specified.

 Rational decomposition is done using a method from Paul S. Wang.
 For a truncated p-adic number \(x = \frac{r}{s}\) the equation
 \( x \cdot s \equiv r\ (\mathrm{mod}\ p^k)\) is solved by extended Euclidean method.
 The power \(k\) depends on the specifiied precision of a p-adic number and affects the upper bounds of numerator and denominator of the reconstructed rational.
