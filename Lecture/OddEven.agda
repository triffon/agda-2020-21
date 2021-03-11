module OddEven where

open import Data.Empty
open import Agda.Builtin.Unit
open import Data.Bool
open import Agda.Builtin.Nat

isEven : Nat -> Bool
isEven 0 = true
isEven 1 = false
isEven (suc (suc n)) = isEven n

isOdd : Nat -> Bool
isOdd 0 = false
isOdd 1 = true
isOdd (suc (suc n)) = isOdd n

data Even' : Nat -> Set where
  ezero : Even' 0
  esuc : {n : Nat} -> Even' n -> Even' (suc (suc n))

data Odd' : Nat -> Set where
  oone : Odd' 1
  osuc : {n : Nat} -> Odd' n -> Odd' (suc (suc n))

sucEvenIsOdd : (n : Nat) -> T (isEven n) -> T (isOdd (suc n))
sucEvenIsOdd zero p = tt
sucEvenIsOdd (suc (suc n)) p = sucEvenIsOdd n p

sucEven'IsOdd' : {n : Nat} -> Even' n -> Odd' (suc n)
sucEven'IsOdd' ezero = oone
sucEven'IsOdd' (esuc p) = osuc (sucEven'IsOdd' p)

