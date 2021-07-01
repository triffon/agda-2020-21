module Homework.LeftistHeap.Common where

open import Lib.Nat
open import Lib.One
open import Lib.Zero
open import Lib.Sum
open import Lib.Eq

Leq : Nat -> Nat -> Set
Leq zero m = One
Leq (suc n) zero = Zero
Leq (suc n) (suc m) = Leq n m

decLeq : (n m : Nat) -> Leq n m + Leq m n
decLeq zero m = inl <>
decLeq (suc n) zero = inr <>
decLeq (suc n) (suc m) = decLeq n m

<=-Leq : {n m : Nat} -> n <= m -> Leq n m
<=-Leq ozero = <>
<=-Leq (osuc p) = <=-Leq p

Leq-refl : (n : Nat) -> Leq n n
Leq-refl n = <=-Leq (<=-refl n)

Leq-trans : (n m k : Nat) -> Leq n m -> Leq m k -> Leq n k
Leq-trans zero m k p q = <>
Leq-trans (suc n) (suc m) (suc k) p q = Leq-trans n m k p q

Priority : Set
Priority = Nat

Rank : Set
Rank = Nat

data Maybe (A : Set) : Set where
  no : Maybe A
  yes : A -> Maybe A

min : Nat -> Nat -> Nat
min n m with decLeq n m
... | inl _ = n
... | inr _ = m

min-Leq-left : (n m : Nat) -> Leq (min n m) n
min-Leq-left n m with decLeq n m
... | inl _ = Leq-refl n
... | inr m<=n = m<=n 

min-right-zero : (m : Nat) -> min m zero == zero
min-right-zero zero = refl
min-right-zero (suc m) = refl

leq-leq-== : (n m : Nat) -> Leq n m -> Leq m n -> n == m
leq-leq-== zero zero _ _ = refl
leq-leq-== (suc n) (suc m) n<=m m<=n rewrite leq-leq-== n m n<=m m<=n = refl

min-symm : (n m : Nat) -> min n m == min m n
min-symm n m with decLeq n m | decLeq m n
... | inl n<=m | inl m<=n = leq-leq-== n m n<=m m<=n
... | inl _ | inr _ = refl
... | inr _ | inl _ = refl
... | inr m<=n | inr n<=m = leq-leq-== m n m<=n n<=m

min-Leq-right : (n m : Nat) -> Leq (min n m) m
min-Leq-right n m with decLeq n m
... | inl n<=m = n<=m
... | inr _ = Leq-refl m
