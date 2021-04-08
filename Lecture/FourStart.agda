{-# OPTIONS --no-unicode #-}

module Lecture.FourStart where

open import Lib.List
open import Lib.Eq
open import Lib.Nat
open import Lib.Sum
open import Lib.One
open import Lib.Zero
open import Lib.Sigma

-- describe modules
-- show example with open

module Listy (A : Set) where
  x : Nat
  x = zero

  id' : A -> A
  id' y = y

  bla : Nat -> Set
  bla n = A

-- z : Nat
-- z = {!id'!}

-- show bst constructions
-- write Bound
-- write LeqBound
-- write BST
-- explain "pushing down constraints"
-- examples for bst
-- show tree diagram

LeqNat : Nat -> Nat -> Set
LeqNat zero m = One
LeqNat (suc n) zero = Zero
LeqNat (suc n) (suc m) = LeqNat n m

_ : 3 <= 5
_ = osuc (osuc (osuc ozero))

_ : LeqNat 3 5
_ = <>

decLeqNat : (n m : Nat) -> LeqNat n m + LeqNat m n
decLeqNat zero _  = inl <>
decLeqNat (suc n) zero = inr <>
decLeqNat (suc n) (suc m) = decLeqNat n m

<=-LeqNat : {n m : Nat} -> n <= m -> LeqNat n m
<=-LeqNat ozero = <>
<=-LeqNat (osuc p) = <=-LeqNat p

module
  Sorting
    (Key : Set)
    (Leq : Key -> Key -> Set)
    (_<=?_ : (x y : Key) -> Leq x y + Leq y x)
  where

  data Bound : Set where
    -inf : Bound
    inKey : Key -> Bound
    +inf : Bound

  LeqBound : Bound -> Bound -> Set
  LeqBound -inf y = One
  LeqBound x +inf = One
  LeqBound (inKey x) (inKey y) = Leq x y
  LeqBound _ _ = Zero

  data BST (lo hi : Bound) : Set where
    empty : LeqBound lo hi -> BST lo hi

    node :
      (k : Key) ->
      (left : BST lo (inKey k)) ->
      (right : BST (inKey k) hi) ->
      BST lo hi

  -- you can use _<=?_ to compare two values
  insert :
    {lo hi : Bound} (k : Key) ->
    LeqBound lo (inKey k) -> LeqBound (inKey k) hi ->
    BST lo hi -> BST lo hi
  insert k lb ub (empty _) = node k (empty lb) (empty ub)
  insert k lb ub (node r lt rt) with k <=? r
  ... | inl k<=r = node r (insert k lb k<=r lt) rt
  ... | inr r<=k = node r lt (insert k r<=k ub rt)

  makeTree : List Key -> BST -inf +inf
  makeTree [] = empty <>
  makeTree (x ,- l) = insert x <> <> (makeTree l)

  -- use the same idea as in BST to define "ordered lists"
  -- be careful about what constraints you need in your recursive case!
  data OList (lo hi : Bound) : Set where
    emptyOL : LeqBound lo hi -> OList lo hi

    consOL :
      (k : Key) ->
      LeqBound lo (inKey k) ->
      OList (inKey k) hi ->
      OList lo hi

  -- append ordered lists
  -- note that we require a key to "bridge" the two lists
  -- try to implement
  -- append : {lo mid hi : Bound} -> OList lo mid -> OList mid hi -> OList lo hi
  -- and see where you get stuck
  appendKeyed : {lo hi : Bound} -> (k : Key) -> OList lo (inKey k) -> OList (inKey k) hi -> OList lo hi
  appendKeyed k (emptyOL lo<=k) rs = consOL k lo<=k rs
  appendKeyed k (consOL x lo<=x ls) rs = consOL x lo<=x (appendKeyed k ls rs) 

  flatten : {lo hi : Bound} -> BST lo hi -> OList lo hi
  flatten (empty lo<=hi) = emptyOL lo<=hi
  flatten (node k lt rt) = appendKeyed k (flatten lt) (flatten rt)

  sort : List Key -> OList -inf +inf
  sort xs = flatten (makeTree xs)

--          2
--       1  .  3
--     <=.<=.<=.<=
--       .  .  .
-- -inf<=1<=2<=3<=+inf

open Sorting Nat LeqNat decLeqNat

one : BST -inf (inKey 2)
one = node 1 (empty <>) (empty <>)

three : BST (inKey 2) +inf
three = node 3 (empty <>) (empty <>)

two : BST -inf +inf
two = node 2 one three

Dec : (A : Set) -> Set
Dec A = (A -> Zero) + A

-- used a module to introduce global vars
-- in here, you can compare values for equality with _==?_
-- in all proofs for functions defined with a `with`
-- you're most likely going to need to do another with
-- because your proof will be stuck on the result of the with in the original function def
module listy {A : Set} {_==?_ : (x y : A) -> Dec (x == y)} where

  infix 10 _In_

  data _In_ (x : A) : List A -> Set where
    here : {xs : List A} -> x In (x ,- xs)
    there : {y : A} {xs : List A} -> x In xs -> x In (y ,- xs)

  +L-monoL-In : {y : A} {ys : List A} -> (xs : List A) -> y In ys -> y In xs +L ys
  +L-monoL-In [] yInys = yInys
  +L-monoL-In (_ ,- xs) yInys = there (+L-monoL-In xs yInys)

  +L-splits-In : {x : A} (xs ys : List A) -> x In xs +L ys -> x In xs + x In ys
  +L-splits-In [] ys p = inr p
  +L-splits-In (x ,- xs) ys here = inl here
  +L-splits-In (x ,- xs) ys (there p) with +L-splits-In xs ys p
  ... | inl xInxs = inl (there xInxs)
  ... | inr yInys = inr yInys

  notIn[] : {x : A} -> x In [] -> Zero
  notIn[] ()

  nowhere : {x y : A} {ys : List A} -> (x == y -> Zero) -> (x In ys -> Zero) -> x In y ,- ys -> Zero
  nowhere x!=y xNotInys here = x!=y refl
  nowhere x!=y xNotInys (there p) = xNotInys p

  -- if there is one, return the first x in the list
  find : (x : A) (xs : List A) -> Dec (x In xs)
  find x [] = inl notIn[]
  find x (y ,- ys) with x ==? y
  find x (y ,- ys) | inl x!=y with find x ys
  find x (y ,- ys) | inl x!=y | inl xNotInys = inl (nowhere x!=y xNotInys)
  find x (y ,- ys) | inl x!=y | inr xInys    = inr (there xInys)
  find x (y ,- ys) | inr refl = inr here

  -- delete all the occurrences of x in the list
  remove : (x : A) -> (xs : List A) -> List A
  remove _ [] = []
  remove x (y ,- ys) with x ==? y
  ... | inl _ = y ,- remove x ys
  ... | inr _ = remove x ys

  remove-removes : (xs : List A) -> (x : A) -> x In remove x xs -> Zero
  remove-removes (y ,- xs) x p with x ==? y
  remove-removes (y ,- xs) .y here     | inl x!=y = x!=y refl
  remove-removes (y ,- xs) x (there p) | inl x!=y = remove-removes xs x p
  ...                                  | inr refl = remove-removes xs x p

  remove-keeps : (xs : List A) (y : A) -> y In xs -> (x : A) -> (x == y -> Zero) -> y In remove x xs
  remove-keeps (z ,- xs) .z here x x!=y with x ==? z
  ... | inl _  = here
  ... | inr refl = zero-elim (x!=y refl)
  remove-keeps (z ,- xs) y (there yInxs) x x!=y with x ==? z
  ... | inl x!=z = there (remove-keeps xs y yInxs x x!=y)
  ... | inr refl = remove-keeps xs y yInxs x x!=y


  -- xs Sub ys - xs is a subsequence of ys
  -- [] Sub []
  -- 5 ,- [] Sub 5 ,- []
  -- 3 ,- 5 ,- [] Sub 3 ,- 5 ,- []
  -- 3 ,- 5 ,- [] Sub 3 ,- 5 ,- 4 ,- []
  -- 3 ,- 5 ,- [] Sub 3 ,- 4 ,- 5 ,- []
  data _Sub_ : List A -> List A -> Set where
    s[] : [] Sub []
    s-cons : {x : A} {xs ys : List A} -> xs Sub ys -> (x ,- xs) Sub (x ,- ys)
    s-skip : {x : A} {xs ys : List A} -> xs Sub ys -> xs Sub (x ,- ys)

  infix 10 _Sub_

  s[]-all : (xs : List A) -> [] Sub xs
  s[]-all [] = s[]
  s[]-all (x ,- xs) = s-skip (s[]-all xs)

  Sub-refl : (xs : List A) -> xs Sub xs
  Sub-refl [] = s[]
  Sub-refl (x ,- xs) = s-cons (Sub-refl xs)

  -- try to make the definition "as lazy" as possible - meaning pattern matching on as few things as possible
  -- this will affect your proof for Sub-trans-assoc
  Sub-trans : {xs ys zs : List A} -> xs Sub ys -> ys Sub zs -> xs Sub zs
  Sub-trans xsSubys s[] = xsSubys
  Sub-trans (s-cons xsSubys) (s-cons ysSubzs) = s-cons (Sub-trans xsSubys ysSubzs)
  Sub-trans (s-skip xsSubys) (s-cons ysSubzs) = s-skip (Sub-trans xsSubys ysSubzs)
  Sub-trans xsSubys          (s-skip ysSubzs) = s-skip (Sub-trans xsSubys ysSubzs)


  +L-monoL-Sub : (xs ys : List A) -> xs Sub (xs +L ys)
  +L-monoL-Sub [] ys = s[]-all ys
  +L-monoL-Sub (x ,- xs) ys = s-cons (+L-monoL-Sub xs ys)

  +L-monoR-Sub : (xs ys : List A) -> xs Sub (ys +L xs)
  +L-monoR-Sub xs [] = Sub-refl xs 
  +L-monoR-Sub xs (x ,- ys) = s-skip (+L-monoR-Sub xs ys)

  Sub-all-In : {xs ys : List A} -> xs Sub ys -> {x : A} -> x In xs -> x In ys
  Sub-all-In (s-cons xsSubys) here = here
  Sub-all-In (s-cons xsSubys) (there xInxs) = there (Sub-all-In xsSubys xInxs)
  Sub-all-In (s-skip xsSubys) xInxs = there (Sub-all-In xsSubys xInxs)

  remove-Sub : (x : A) (xs : List A) -> remove x xs Sub xs
  remove-Sub x [] = s[]
  remove-Sub x (y ,- xs) with x ==? y
  ... | inl _ = s-cons (remove-Sub x xs)
  ... | inr _ = s-skip (remove-Sub x xs)

  -- might need to make an implicit arg explicit in one of the cases
  remove-preserves-Sub : {xs ys : List A} (x : A) -> xs Sub ys -> remove x xs Sub ys
  remove-preserves-Sub  x s[] = s[]
  remove-preserves-Sub {(y ,- xs)} {(y ,- ys)} x (s-cons xsSubys) with x ==? y
  ... | inl _ = s-cons (remove-preserves-Sub x xsSubys)
  ... | inr _ = s-skip (remove-preserves-Sub x xsSubys)
  remove-preserves-Sub x (s-skip xsSubys) = s-skip (remove-preserves-Sub x xsSubys)

  ,-Sub-remove : {xs ys : List A} (x : A) -> xs Sub x ,- ys -> remove x xs Sub ys
  -- awful! :(
  ,-Sub-remove x (s-cons p) with x ==? x
  ... | inl x!=x = zero-elim (x!=x refl)
  ... | inr x==x = remove-preserves-Sub x p
  ,-Sub-remove x (s-skip p)        = remove-preserves-Sub x p

  Sub-trans-assoc :
    {xs ys zs vs : List A} (sub1 : xs Sub ys) (sub2 : ys Sub zs) (sub3 : zs Sub vs) ->
    Sub-trans (Sub-trans sub1 sub2) sub3 == Sub-trans sub1 (Sub-trans sub2 sub3)
  Sub-trans-assoc sub1 sub2 s[] = refl
  Sub-trans-assoc sub1          (s-skip sub2) (s-cons sub3) rewrite Sub-trans-assoc sub1 sub2 sub3 = refl
  Sub-trans-assoc (s-cons sub1) (s-cons sub2) (s-cons sub3) rewrite Sub-trans-assoc sub1 sub2 sub3 = refl
  Sub-trans-assoc (s-skip sub1) (s-cons sub2) (s-cons sub3) rewrite Sub-trans-assoc sub1 sub2 sub3 = refl
  Sub-trans-assoc sub1          sub2          (s-skip sub3) rewrite Sub-trans-assoc sub1 sub2 sub3 = refl

{-
decNatEq : (n m : Nat) -> Dec (n == m)
decNatEq = {!!}

open listy {Nat} {decNatEq}

_ : 3 In 3 ,- 5 ,- []
_ = here

_ : 5 In 3 ,- 5 ,- []
_ = there here

5notIn[] : 5 In [] -> Zero
5notIn[] ()

5notIn3 : 5 In 3 ,- [] -> Zero
5notIn3 (there ())

_ : [] Sub []
_ = s[]

_ : 5 ,- [] Sub 5 ,- []
_ = s-cons s[]

_ : 3 ,- 5 ,- [] Sub 3 ,- 5 ,- []
_ = s-cons (s-cons s[])

_ : 3 ,- 5 ,- [] Sub 3 ,- 5 ,- 4 ,- []
_ = s-cons (s-cons (s-skip s[]))

_ : 3 ,- 5 ,- [] Sub 3 ,- 4 ,- 5 ,- []
_ = s-cons (s-skip (s-cons s[]))

32notSub23 : 3 ,- 2 ,- [] Sub 2 ,- 3 ,- [] -> Zero
32notSub23 (s-skip (s-cons ()))
32notSub23 (s-skip (s-skip ()))

332notSub32 : 3 ,- 3 ,- 2 ,- [] Sub 3 ,- 2 ,- [] -> Zero
332notSub32 (listy.s-cons (listy.s-skip ()))
332notSub32 (listy.s-skip (listy.s-skip ()))
-}
