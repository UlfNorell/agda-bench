
module Sums where

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Strict

downFrom : Nat → List Nat
downFrom zero    = []
downFrom (suc n) = n ∷ downFrom n

module _ {a b} {A : Set a} {B : Set b} where

  foldr : (A → B → B) → B → List A → B
  foldr f z []       = z
  foldr f z (x ∷ xs) = f x (foldr f z xs)

  foldl : (B → A → B) → B → List A → B
  foldl f z []       = z
  foldl f z (x ∷ xs) = foldl f (f z x) xs

  foldl! : (B → A → B) → B → List A → B
  foldl! f z []       = z
  foldl! f z (x ∷ xs) = primForce (f z x) λ z′ → foldl! f z′ xs

sum-foldr : List Nat → Nat
sum-foldr = foldr _+_ 0

sum-foldl : List Nat → Nat
sum-foldl = foldl _+_ 0

sum-foldl! : List Nat → Nat
sum-foldl! = foldl! _+_ 0

sum-rec : List Nat → Nat
sum-rec []       = 0
sum-rec (x ∷ xs) = x + sum-rec xs

sum-acc : Nat → List Nat → Nat
sum-acc z [] = z
sum-acc z (x ∷ xs) = sum-acc (z + x) xs

sum-acc-m : Nat → List Nat → Nat
sum-acc-m z [] = z
sum-acc-m 0 (x ∷ xs) = sum-acc-m x xs
sum-acc-m z (x ∷ xs) = sum-acc-m (z + x) xs

sum-acc! : Nat → List Nat → Nat
sum-acc! z [] = z
sum-acc! z (x ∷ xs) = primForce (z + x) λ z′ → sum-acc! z′ xs

last : Nat → List Nat → Nat
last z [] = 0
last _ (x ∷ xs) = last x xs

test : (List Nat → Nat) → Nat → Nat
test f n = f (downFrom n)

n = 10000

bench-foldl  = test sum-foldl n
bench-foldl! = test sum-foldl! n
bench-foldr  = test sum-foldr n
bench-rec    = test sum-rec n
bench-acc    = test (sum-acc 0) n
bench-acc!   = test (sum-acc! 0) n
bench-acc-m  = test (sum-acc-m 0) n
bench-last   = test (last 0) n
