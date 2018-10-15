## AgdaBench

A tool for benchmarking compile-time (type-checking time) performance of Agda
programs. It is implemented as an Agda backend, which means that it functions
as a full Agda compiler, with additional arguments for the benchmarking. The
benchmarking is done using the
[Criterion](http://hackage.haskell.org/package/criterion) library.

### Example

A criterion benchmark is created for each top-level value in the given Agda
module whose name starts with `bench`, and calling the tool with an Agda file
will run each of the benchmarks and measure the time it takes to reduce them to
weak-head normal form (or normal form if the `--nf` flag is given). For
instance, given the module

```agda
module Example where

open import Agda.Builtin.Nat
open import Agda.Builtin.List

downFrom : Nat → List Nat
downFrom zero    = []
downFrom (suc n) = n ∷ downFrom n

sum-rec : List Nat → Nat
sum-rec []       = 0
sum-rec (x ∷ xs) = x + sum-rec xs

sum-acc : Nat → List Nat → Nat
sum-acc z [] = z
sum-acc z (x ∷ xs) = sum-acc (z + x) xs

sum-acc! : Nat → List Nat → Nat
sum-acc! z [] = z
sum-acc! 0 (x ∷ xs) = sum-acc! x xs
sum-acc! z (x ∷ xs) = sum-acc! (z + x) xs

n = 10000
bench-rec  = sum-rec    (downFrom n)
bench-acc  = sum-acc  0 (downFrom n)
bench-acc! = sum-acc! 0 (downFrom n)
```

we can invoke `agda-bench` as

```
$ agda-bench Example.agda
Benchmarks:
  bench-rec = 49995000
  bench-acc = 49995000
  bench-acc! = 49995000

benchmarking bench-rec
time                 16.71 ms   (16.12 ms .. 17.60 ms)
                     0.986 R²   (0.968 R² .. 0.997 R²)
mean                 17.19 ms   (16.78 ms .. 17.76 ms)
std dev              1.203 ms   (822.0 μs .. 1.709 ms)
variance introduced by outliers: 29% (moderately inflated)

benchmarking bench-acc
time                 31.69 ms   (30.80 ms .. 32.71 ms)
                     0.997 R²   (0.994 R² .. 0.999 R²)
mean                 32.35 ms   (31.67 ms .. 33.92 ms)
std dev              2.064 ms   (1.061 ms .. 3.637 ms)
variance introduced by outliers: 22% (moderately inflated)

benchmarking bench-acc!
time                 10.61 ms   (10.52 ms .. 10.71 ms)
                     0.999 R²   (0.998 R² .. 1.000 R²)
mean                 10.83 ms   (10.73 ms .. 10.93 ms)
std dev              266.5 μs   (203.0 μs .. 381.2 μs)
```

Individual benchmarks can be run by giving the `-B name-of-benchmark` flag. The
`-B` flag passes along its argument to the Criterion driver. Use `-B --help`
for more information.

To benchmark an expression that isn't bound to a top-level `bench` definition you can
use the `-C EXPR` flag:

```
$ agda-bench Example.agda -C "sum-rec (downFrom 100)"
benchmarking sum-rec (downFrom 100)
time                 107.0 μs   (105.5 μs .. 108.7 μs)
                     0.998 R²   (0.997 R² .. 0.999 R²)
mean                 107.6 μs   (106.7 μs .. 109.0 μs)
std dev              3.532 μs   (2.379 μs .. 4.833 μs)
variance introduced by outliers: 32% (moderately inflated)
```

The full list of options (not including the Criterion options) are:

```
benchmark backend options
  -B ARGS  --bench-options=ARGS  Benchmarking options. Use -B --help for more information.
  -s EXPR  --single=EXPR         Evaluate a single expression
  -C EXPR  --custom=EXPR         Add a custom benchmark for EXPR
  -n       --nf                  Full normalisation instead of weak-head reduction
           --call-by-name        Use call-by-name
```
