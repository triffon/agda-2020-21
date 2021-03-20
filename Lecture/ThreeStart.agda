{-# OPTIONS --no-unicode #-}

module Lecture.ThreeStart where

open import Lib.Nat
open import Lib.Eq
open import Lib.List
open import Lib.One
open import Lib.Zero
open import Lib.Two
open import Lib.Sum

-- !show rewrite

-- maybe send link on actual rewrite
+N-right-zero' : (n : Nat) -> n +N 0 == n
+N-right-zero' zero = refl zero
+N-right-zero' (suc n) rewrite +N-right-zero' n = refl _

-- rewrite allows us to replace "by an equality"

-- +N-right-zero' n : n +N 0 == n
-- suc (n +N 0) == suc n

-- 3 + n
-- n == m
-- 3 + m


-- James McKinna, Conor McBride
-- !show with
-- !don't forget to say what the three dots mean!!
-- !demonstrate that when we match, goal changes
-- !show lambda
-- !?show where
-- !?show "generate helper"
-- decide

-- refl
-- suc n == suc m
-- suc n == suc n
-- n ~ m
not-eq-suc : {n m : Nat} -> (n == m -> Zero) -> suc n == suc m -> Zero
not-eq-suc notn==m (refl _) = notn==m (refl _)

-- (\ x y z -> x + y + z) 1 2 3 == 6
dec== : (n m : Nat) -> n == m + (n == m -> Zero)
dec== zero zero = inl (refl zero)
dec== zero (suc m) = inr \() -- refine, <SPC> m r
dec== (suc n) zero = inr \()
dec== (suc n) (suc m) with dec== n m
dec== (suc n) (suc .n) | inl (refl .n) = inl (refl (suc n))
dec== (suc n) (suc m) | inr notp = inr (not-eq-suc notp)
-- <SPC> m h
-- with abstraction
-- unordered_map<T, bool>

--  where
--  helper :
--    {n m : Nat} ->
--    n == m + (n == m -> Zero) ->
--    suc n == suc m + (suc n == suc m -> Zero)
--  helper (inl p) = inl (ap suc p)
--  helper (inr notp) = inr \ q -> not-eq-suc notp q

_ : 3 == 2 + (3 == 2 -> Zero)
_ = dec== 3 2

bla : (n : Nat) -> n == 2 -> 2 +N n == 4
bla .2 (refl .2) = refl 4

-- case dec== n 2 of
--   inl p -> bla n p
--   inr notp -> putStrLn "invalid input"

Even : Nat -> Set
Even zero = One
Even (suc zero) = Zero -- 1
Even (suc (suc n)) = Even n -- 2 + n

-- !explain how this is an "exists"
-- !examples!
-- !do these on another "live solving session" instead:
-- show how this generalises _+_ ?
-- and how (a : A) -> P a generalises _*_ ?
record _><_ (A : Set) (P : A -> Set) : Set where
  constructor _,_

  field
    fst : A
    snd : P fst

-- record Customer
--   field
--     age : Int
--     alcohol : if age > 18 then List Drink else One

-- data Sg (A : Set) (P : A -> Set) : Set where
--   sg : (fst : A) -> P fst -> Sg A P

open _><_ public

infixr 8 _><_

_ : Nat >< \n -> Nat >< \m -> n == m
_ = zero , (zero , refl zero)

-- (a : A) -> ...
-- ∀(a ∈ A).  ...
-- ∃(n ∈ Nat). Even n
_ : Nat >< \n -> Even n
_ = 2 , <>

_*_ : Set -> Set -> Set
A * B = A >< \ _ -> B
infixr 9 _*_

_ : Nat * Nat
_ = zero , zero


data Vec (A : Set) : Nat -> Set where
  [] : Vec A zero
  _,-_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)


-- lHead : {A : Set}-> List A -> A
-- lHead [] = {!error "Prelude.head empty list !}
-- lHead (x ,- _) = x

vHead : {A : Set} {n : Nat} -> Vec A (suc n) -> A
vHead (x ,- _) = x


vTail : {A : Set} {n : Nat} -> Vec A (suc n) -> Vec A n
vTail (_ ,- xs) = xs

-- !?show parallel with +L - agda can now write it itself
_+L'_ : {A : Set} -> List A -> List A -> List A
[] +L' ys = ys
(x ,- xs) +L' ys = x ,- (xs +L' ys)

_+V_ : {A : Set} {n m : Nat} -> Vec A n -> Vec A m -> Vec A (n +N m)
[] +V ys = ys
(x ,- xs) +V ys = x ,- (xs +V ys)


infixr 12 _+V_

-- readLn :: [Char]
-- input <- readLn
--
-- case listToVec input of
-- zero, [] -> putStLn "invalid input"
-- suc n, v -> isLengthMoreThan10 v n
--
-- 10 <= n

listToVec : {A : Set} -> List A -> Nat >< \ n -> Vec A n
listToVec [] = zero , []
listToVec (x ,- xs) =
  let n , xs' = listToVec xs
  in suc n , (x ,- xs')

_=[]_ : {A : Set} {y : A} -> (x : A) -> x == y -> x == y
x =[] (refl _) = refl _

infixr 1 _=[]_

_=[_>=_ : {A : Set} {y z : A} -> (x : A) -> x == y -> y == z -> x == z
x =[ refl _ >= (refl _) = refl _

infixr 1 _=[_>=_

_=<_]=_ : {A : Set} {y z : A} -> (x : A) -> y == z -> x == y -> x == z
x =< refl _ ]= (refl _) = refl _

infixr 1 _=<_]=_

_QED : {A : Set} -> (x : A) -> x == x
x QED = refl x

infix 3 _QED

-- n == // защото n е пешо и гошо
-- m == // защото лагранж
-- z QED

-- ! show =[] for zero case?
-- ! show eq reasoning with commut
-- ! maybe write out eq reasoning?

+N-commut' : (n m : Nat) -> n +N m == m +N n
+N-commut' zero m =
  m
    =[ ==-symm (+N-right-zero m) >=
  m +N zero
    QED
+N-commut' (suc n) m =
  suc (n +N m)
    =[ ap suc (+N-commut' n m) >=
  suc (m +N n)
    =[ ==-symm (+N-right-suc m n) >=
  m +N suc n
    QED


<=-refl : (n : Nat) -> n <= n
<=-refl zero = ozero
<=-refl (suc n) = osuc (<=-refl n)

<=-antisym : {n m : Nat} -> n <= m -> m <= n -> n == m
<=-antisym ozero ozero = refl _
<=-antisym (osuc p) (osuc q) rewrite <=-antisym p q = refl _

<=-mono-left-+ : {n m : Nat} (k : Nat) -> n <= m -> k +N n <= k +N m
<=-mono-left-+ zero p = p
<=-mono-left-+ (suc k) p = osuc (<=-mono-left-+ k p)

<=-right-+ : {m : Nat} (n : Nat) -> n <= m +N n
<=-right-+ zero = ozero
-- can we do it smoothly without explicitating m?
<=-right-+ {m} (suc n) rewrite +N-right-suc m n = osuc (<=-right-+ n)

-- you might need a lemma here
<=-mono-right-+ : {n m : Nat} (k : Nat) -> n <= m -> n +N k <= m +N k
-- <=-mono-right-+ {n} {m} k rewrite +N-commut n k | +N-commut m k = <=-mono-left-+ {n} {m} k
<=-mono-right-+ k ozero = <=-right-+ k
<=-mono-right-+ k (osuc p) = osuc (<=-mono-right-+ k p)

-- multiplication using repeated addition
_*N_ : Nat -> Nat -> Nat
zero *N m = zero
suc n *N m = m +N n *N m
infixr 40 _*N_

-- EXERCISE: multiplication right identity
*N-right-id : (n : Nat) -> n *N 1 == n
*N-right-id zero = refl _
*N-right-id (suc n) rewrite *N-right-id n = refl _

-- multiplication distributes over addition
*N-distrib-+N : (n m k : Nat) -> (n +N m) *N k == n *N k +N m *N k
*N-distrib-+N zero m k = refl _
*N-distrib-+N (suc n) m k rewrite *N-distrib-+N n m k = ==-symm (+N-assoc k _ _)

-- use *N-distrib-+N
*N-assoc : (n m k : Nat) -> (n *N m) *N k == n *N (m *N k)
*N-assoc zero m k = refl _
*N-assoc (suc n) m k rewrite *N-distrib-+N m (n *N m) k | *N-assoc n m k = refl _

*N-right-zero : (n : Nat) -> zero == n *N zero
*N-right-zero zero = refl _
*N-right-zero (suc n) = *N-right-zero n

*N-right-suc : (n m : Nat) -> m +N m *N n == m *N suc n
*N-right-suc n zero = refl _
*N-right-suc n (suc m) rewrite ==-symm (*N-right-suc n m) |
                               ==-symm (+N-assoc m n (m *N n)) |
                               ==-symm (+N-assoc n m (m *N n)) |
                               +N-commut n m = refl _


-- figure out what lemmas you need
*N-commut : (n m : Nat) -> n *N m == m *N n
*N-commut zero m = *N-right-zero m
*N-commut (suc n) m rewrite *N-commut n m = *N-right-suc n m

length-+L-distrib : {A : Set} -> (xs ys : List A) -> length (xs +L ys) == length xs +N length ys
length-+L-distrib [] ys = refl _
length-+L-distrib (x ,- xs) ys rewrite length-+L-distrib xs ys = refl _

vecToList : {A : Set} {n : Nat} -> Vec A n -> List A
vecToList [] = []
vecToList (x ,- v) = x ,- vecToList v

vecToList-listToVec-id : {A : Set} -> (xs : List A) -> vecToList (snd (listToVec xs)) == xs
vecToList-listToVec-id [] = refl _
vecToList-listToVec-id (x ,- xs) rewrite vecToList-listToVec-id xs = refl _

vTake : {A : Set} {m n : Nat} -> n <= m -> Vec A m -> Vec A n
vTake ozero _ = []
vTake (osuc p) (x ,- xs) = x ,- vTake p xs

-- you need to have implemented <=-refl before this
vTake-id : {A : Set} (n : Nat) (v : Vec A n) -> vTake (<=-refl n) v == v
vTake-id zero [] = refl _
vTake-id (suc n) (x ,- xs) rewrite vTake-id n xs = refl _

-- m - n
-- d for difference
difference<= : (m n : Nat) -> n <= m -> Nat >< \d -> m == n +N d
difference<= m .0 ozero = m , refl m
difference<= (suc m) (suc n) (osuc p) with difference<= m n p
... | d , q rewrite q = d , refl _

-- naively reverse a list, by appending at the end
reverse : {A : Set} -> List A -> List A
reverse [] = []
reverse (x ,- l) = reverse l +L (x ,- [])


_ : reverse (1 ,- 2 ,- 3 ,- []) == 3 ,- 2 ,- 1 ,- []
_ = refl _

-- might need +L-assoc here
reverse-+L-distrib : {A : Set} (xs ys : List A) -> reverse (xs +L ys) == reverse ys +L reverse xs
reverse-+L-distrib [] ys = ==-symm (+L-right-id (reverse ys))
reverse-+L-distrib (x ,- xs) ys rewrite reverse-+L-distrib xs ys = +L-assoc (reverse ys) _ _

-- might need reverse-+L-distrib here
reverse-involut : {A : Set} (xs : List A) -> reverse (reverse xs) == xs
reverse-involut [] = refl _
reverse-involut (x ,- xs) rewrite reverse-+L-distrib (reverse xs) (x ,- []) |
                                  reverse-involut xs = refl _

-- helper for the linear reverse
-- accumulates the elements of first list, one by one, at the front of the second
-- like how we traditionally implement a linear reverse
-- see the examples below
go : {A : Set} -> List A -> List A -> List A
go [] ys = ys
go (x ,- xs) ys = go xs (x ,- ys)

_ : go (1 ,- 2 ,- []) [] == 2 ,- 1 ,- []
_ = refl _

_ : go (1 ,- 2 ,- []) (4 ,- 5 ,- []) == 2 ,- 1 ,- 4 ,- 5 ,- []
_ = refl _


-- implement an O(n) reverse by using go
linear-reverse : {A : Set} -> List A -> List A
linear-reverse xs = go xs []

-- a lemma that will be useful for proving that linear-reverse acts the same as reverse
go-reverse : {A : Set} (xs ys : List A) -> go xs ys == reverse xs +L ys
go-reverse [] ys = refl _
go-reverse (x ,- xs) ys rewrite go-reverse xs (x ,- ys) |
                                +L-assoc (reverse xs) (x ,- []) ys = refl _

linear-reverse-is-reverse : {A : Set} (xs : List A) -> linear-reverse xs == reverse xs
linear-reverse-is-reverse [] = refl _
linear-reverse-is-reverse (x ,- xs) rewrite linear-reverse-is-reverse xs = go-reverse xs (x ,- [])

map : {A B : Set} -> (A -> B) -> List A -> List B
map f [] = []
map f (x ,- xs) = f x ,- map f xs

map-+L-distrib : {A B : Set} -> (f : A -> B) -> (xs ys : List A) -> map f (xs +L ys) == map f xs +L map f ys
map-+L-distrib f [] ys = refl _
map-+L-distrib f (x ,- xs) ys rewrite map-+L-distrib f xs ys = refl _

id : {A : Set} -> A -> A
id x = x

map-id : {A : Set} (xs : List A) -> map id xs == xs
map-id [] = refl _
map-id (x ,- xs) rewrite map-id xs = refl _

_<<_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
(f << g) x = f (g x)

map-compose : {A B C : Set} -> (f : B -> C) (g : A -> B) -> (xs : List A) -> map (f << g) xs == map f (map g xs)
map-compose f g [] = refl _
map-compose f g (x ,- xs) rewrite map-compose f g xs = refl _

foldr : {A B : Set} -> (A -> B -> B) -> B -> List A -> B
foldr op nv [] = nv
foldr op nv (x ,- xs) = op x (foldr op nv xs)

foldr-+L :
  {A B : Set}
  (f : A -> B -> B)
  (xs ys : List A)
  (v : B) ->
  foldr f (foldr f v ys) xs == foldr f v (xs +L ys)
foldr-+L op [] ys nv = refl _
foldr-+L op (x ,- xs) ys nv rewrite foldr-+L op xs ys nv = refl _

map-foldr :
  {A B : Set}
  (f : A -> B)
  (xs : List A) ->
  map f xs == foldr (\x r -> f x ,- r) [] xs
map-foldr f [] = refl _
map-foldr f (x ,- xs) rewrite map-foldr f xs = refl _

-- uh.. do trees?

-- good example to show how rewrite is implemented, maybe
-- but don't make students solve this
listToVec-vecToList-id : {A : Set} {n : Nat} -> (v : Vec A n) -> listToVec (vecToList v) == n , v
listToVec-vecToList-id [] = refl _
listToVec-vecToList-id (x ,- xs) rewrite listToVec-vecToList-id xs = refl _
