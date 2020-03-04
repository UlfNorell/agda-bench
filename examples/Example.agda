
module Example where

open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Equality

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
