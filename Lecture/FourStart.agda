{-# OPTIONS --no-unicode #-}

module Lecture.FourStart where

open import Lib.List
open import Lib.Vec
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

-- TODO:
-- grey highlight

-- plusnat : Nat -> Nat -> Nat
-- plusnat zero m = m
-- plusnat n zero = n
-- plusnat (suc n) m = suc (plusnat n m)
--
-- f : (m : Nat) -> plusnat zero m == m
-- f m = refl
--
-- g : (m : Nat) -> plusnat m zero == m
-- g zero = {!!}
-- g (suc m) = {!!}

-- case n of
--   zero -> m
--   suc n ->
--     case m of
--       zero -> n
--       ...

-- plusnat n m == plusnat m n // n -> zero
-- plusnat zero m -> m
-- Goal: m == plusnat m zero
-- m == m
-- plusnat-commut : (n m : Nat) -> plusnat n m == plusnat m n
-- plusnat-commut zero m = {!!}
-- plusnat-commut (suc n) m = {!!}

-- "pipe"s in goal
-- with generalises (show vs lambda)
-- show generalised:
-- goal type

-- original args
-- other later withs
--
-- dots ??

-- asd : Nat -> Nat
-- asd n with decLeqNat n 5
-- ... | inl x = 5
-- ... | inr x = n
--
-- pasd : (n : Nat) -> LeqNat 5 n -> asd n == n
-- pasd n x with decLeqNat n 5
-- ... | inl x1 = {!!}
-- ... | inr x1 = {!!}


-- bla : (n : Nat) -> n == 10 -> 0 == n
-- bla n x with n
-- ... | z = {!z!}
--
-- bla2 : (n : Nat) -> 0 == n
-- bla2 n with n
-- bla2 n | zero with 5
-- bla2 n | zero | q = {!!}
-- bla2 n | suc z = {!!}

-- pasd : (n : Nat) -> 6 <= n -> asd n == n
-- pasd = {!!}

-- +N-right-zero' : (n : Nat) -> n +N 0 == n
-- +N-right-zero' zero = refl
-- -- +N-right-zero' (suc n) rewrite +N-right-zero' n = refl
-- +N-right-zero' (suc n) with n +N 0 with +N-right-zero' n
-- ... | .n | refl = refl

-- Goal: suc (n +N 0) == suc n
-- ————————————————————————————————————————————————————————————
-- z : n +N 0 == n
-- n : Nat
-- after
-- Goal: suc u == suc n
-- ————————————————————————————————————————————————————————————
-- z : u == n
-- u : Nat
-- n : Nat

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
  ... | inr refl = inr here
  ... | inl x!=y with find x ys
  ... | inl xNotInys = inl (nowhere x!=y xNotInys)
  ... | inr xInys    = inr (there xInys)

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

  ==?-refl : (x : A) -> x ==? x == inr refl
  ==?-refl x with x ==? x
  ... | inl x!=x = zero-elim (x!=x refl)
  ... | inr refl = refl

  ,-Sub-remove : {xs ys : List A} (x : A) -> xs Sub x ,- ys -> remove x xs Sub ys
  ,-Sub-remove x (s-cons p) rewrite ==?-refl x = remove-preserves-Sub x p
  ,-Sub-remove x (s-skip p)                    = remove-preserves-Sub x p

  Sub-trans-assoc :
    {xs ys zs vs : List A} (sub1 : xs Sub ys) (sub2 : ys Sub zs) (sub3 : zs Sub vs) ->
    Sub-trans (Sub-trans sub1 sub2) sub3 == Sub-trans sub1 (Sub-trans sub2 sub3)
  Sub-trans-assoc sub1 sub2 s[] = refl
  Sub-trans-assoc sub1          (s-skip sub2) (s-cons sub3) rewrite Sub-trans-assoc sub1 sub2 sub3 = refl
  Sub-trans-assoc (s-cons sub1) (s-cons sub2) (s-cons sub3) rewrite Sub-trans-assoc sub1 sub2 sub3 = refl
  Sub-trans-assoc (s-skip sub1) (s-cons sub2) (s-cons sub3) rewrite Sub-trans-assoc sub1 sub2 sub3 = refl
  Sub-trans-assoc sub1          sub2          (s-skip sub3) rewrite Sub-trans-assoc sub1 sub2 sub3 = refl

decNatEq : (n m : Nat) -> Dec (n == m)
decNatEq zero zero = inr refl
decNatEq zero (suc m) = inl (\ ())
decNatEq (suc n) zero = inl (\ ())
decNatEq (suc n) (suc m) with decNatEq n m
... | inl n!=m = inl (\{ refl -> n!=m refl })
... | inr refl = inr refl

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

-- implement less than or equal for nats, but in a different way
-- look at _Sub_ and think how to "strip away" all the information Lists have compared to Nats
-- the S is because it's similar to Sub, and because I need another name
-- (also for "selection" I guess)
data _<S=_ : Nat -> Nat -> Set where
  o-zero : 0 <S= 0
  o-skip : {n m : Nat} -> n <S= m -> n <S= suc m
  o-succ : {n m : Nat} -> n <S= m -> suc n <S= suc m

_ : 1 <S= 1
_ = o-succ o-zero

_ : 1 <S= 3
_ = o-succ (o-skip (o-skip o-zero))

_ : 3 <S= 5
_ = o-succ (o-succ (o-succ (o-skip (o-skip o-zero))))


-- in general there's more than one way in which n <S= m!
-- find out all the ways

_ :
  (1 <S= 2) >< \p -> -- there's a proof p for 1 <S= 2
  (1 <S= 2) >< \q -> -- and a proof q for 1 <S= 2
  p == q -> Zero     -- and they're different
_ = o-succ (o-skip o-zero), o-skip (o-succ o-zero) , \()

-- it might be interesting to try to figure out how many proofs there are for n <S= m, for fixed n and m
-- you can use -l in a hole for such a proof (e.g. 1 <S= 4), together with agdas auto, to get it to list all of them

-- we can have an "empty" sub - it selects nothing
-- this makes more sense once you reach select - so if you want to you can read the comment on select first
-- alternatively you can think of it as "just a proof"
0<S= : (n : Nat) -> 0 <S= n
0<S= zero = o-zero
0<S= (suc n) = o-skip (0<S= n)

-- similarly, we can have an "all" sub - it selects everything
-- or alternatively, a reflexivity proof
refl-<S= : (n : Nat) -> n <S= n
refl-<S= zero = o-zero
refl-<S= (suc n) = o-succ (refl-<S= n)

-- there is only one empty sub (and only one proof) - and that's the one you wrote
0<S=-unique : {n : Nat} (p : 0 <S= n) -> 0<S= n == p
0<S=-unique o-zero = refl
0<S=-unique (o-skip p) rewrite 0<S=-unique p = refl

-- we can construct a sub from our usual leq
<=-<S= : {n m : Nat} -> n <= m -> n <S= m
<=-<S= {m = 0} ozero = o-zero
<=-<S= {m = suc m} ozero = o-skip (<=-<S= ozero)
<=-<S= {m = suc m} (osuc p) = o-succ (<=-<S= p)

<=-suc : (m : Nat) -> m <= suc m
<=-suc zero = ozero
<=-suc (suc m) = osuc (<=-suc m)

-- and vice versa
-- you might need <=-trans here and an additonal lemma for one of the cases
<S=-<= : {n m : Nat} -> n <S= m -> n <= m
<S=-<= o-zero = ozero
<S=-<= {m = suc m} (o-skip p) = <=-trans (<S=-<= p) (<=-suc m)
<S=-<= (o-succ p) = osuc (<S=-<= p)

-- we can use <S= to encode a "choice of elements" from a vector
-- this is similar in purpose to _Sub_
-- but uses less information than _Sub_, which potentially carries around lists as its arguments (look in the constructors) as we only store Nats
--
-- use the <S= proof to guide you on when to keep an element and when to drop one
select : {A : Set} {m n : Nat} -> n <S= m -> Vec A m -> Vec A n
select o-zero [] = []
select (o-skip p) (x ,- v) = select p v
select (o-succ p) (x ,- v) = x ,- select p v

-- we can compose selections
-- alternatively, this is transitivity for <S=
-- make this as lazy as possible in its pattern matches (so as few matches as possible)
-- so that your later proofs are also easier!
-- hint: match on the right one first
_S<<_ : {n m k : Nat} -> n <S= m -> m <S= k -> n <S= k
o-zero S<< o-zero = o-zero
o-zero S<< o-skip q = o-skip q
o-skip p S<< o-skip q = o-skip (o-skip p S<< q)
-- this is the o-succ-rightmost proof
o-succ p S<< o-skip q = o-skip (o-succ p S<< q)
-- alternative: the o-succ-leftmost proof:
-- o-succ p S<< o-skip q = o-succ (o-skip p S<< q)
o-skip p S<< o-succ q = o-skip (p S<< q)
o-succ p S<< o-succ q = o-succ (p S<< q)

-- selecting a composition is the same as composing selects
-- it doesn't matter if we select a composition or select twice
-- (or in other words, it doesn't matter whether compose first or select first)
select-S<< :
  {A : Set} {n m k : Nat}
  (p : n <S= m) (q : m <S= k) (xs : Vec A k) ->
  select (p S<< q) xs == select p (select q xs)
select-S<< o-zero o-zero [] = refl
select-S<< o-zero (o-skip q) (x ,- xs) with select q xs
... | [] = refl
select-S<< (o-skip p) (o-skip q) (x ,- xs) = select-S<< (o-skip p) q xs
select-S<< (o-succ p) (o-skip q) (x ,- xs) = select-S<< (o-succ p) q xs
select-S<< (o-skip p) (o-succ q) (x ,- xs) = select-S<< p q xs
select-S<< (o-succ p) (o-succ q) (x ,- xs) rewrite select-S<< p q xs = refl

-- it doesn't matter if we compose with the id selection on the left
S<<-left-id : {n m : Nat} (p : n <S= m) -> (refl-<S= n S<< p) == p
S<<-left-id o-zero = refl
S<<-left-id {zero}  (o-skip p) = refl
S<<-left-id {suc n} (o-skip p) rewrite S<<-left-id p = refl
S<<-left-id (o-succ p)         rewrite S<<-left-id p = refl

-- or on the right
S<<-right-id : {n m : Nat} (p : n <S= m) -> (p S<< (refl-<S= m)) == p
S<<-right-id o-zero = refl
S<<-right-id {zero}  (o-skip p) rewrite S<<-right-id p = refl
S<<-right-id {suc n} (o-skip p) rewrite S<<-right-id p = refl
S<<-right-id (o-succ p)         rewrite S<<-right-id p = refl

-- and it's also associative
S<<-assoc :
  {n m k v : Nat} (p : n <S= m) (q : m <S= k) (t : k <S= v) ->
  (p S<< q) S<< t == p S<< (q S<< t)

S<<-assoc o-zero o-zero o-zero = refl
S<<-assoc o-zero o-zero (o-skip t) = refl
S<<-assoc o-zero (o-skip q) (o-skip t) = refl
S<<-assoc o-zero (o-skip q) (o-succ t) = refl
S<<-assoc (o-skip p) (o-skip q) (o-skip t) rewrite S<<-assoc (o-skip p) (o-skip q) t = refl
S<<-assoc (o-skip p) (o-skip q) (o-succ t) rewrite S<<-assoc (o-skip p) q t = refl
S<<-assoc (o-skip p) (o-succ q) (o-skip t) rewrite S<<-assoc (o-skip p) (o-succ q) t = refl
S<<-assoc (o-skip p) (o-succ q) (o-succ t) rewrite S<<-assoc p q t = refl
S<<-assoc (o-succ p) (o-skip q) (o-skip t) rewrite S<<-assoc (o-succ p) (o-skip q) t = refl
S<<-assoc (o-succ p) (o-skip q) (o-succ t) rewrite S<<-assoc (o-succ p) q t = refl
S<<-assoc (o-succ p) (o-succ q) (o-skip t) rewrite S<<-assoc (o-succ p) (o-succ q) t = refl
S<<-assoc (o-succ p) (o-succ q) (o-succ t) rewrite S<<-assoc p q t = refl

-- we can use selections of a particular form to index into a vector
-- a selection with 1 on the left effectively means that there is only one place in its construction that can have a o-succ constructor
-- that's *exactly* the index of the item we want to get from the vector
-- (use select and vHead)
vProject : {A : Set} {n : Nat} -> Vec A n -> 1 <S= n -> A
vProject (x ,- v) (o-skip p) = vProject v p
vProject (x ,- v) (o-succ p) = x

-- note the locations of the "up arrows"

_ : vProject (0 ,- 1 ,- 2 ,- []) (o-succ (o-skip (o-skip o-zero))) == 0
--            ^                   ^
_ = refl

_ : vProject (0 ,- 1 ,- 2 ,- []) (o-skip (o-succ (o-skip o-zero))) == 1
--                 ^                      ^
_ = refl

_ : vProject (0 ,- 1 ,- 2 ,- []) (o-skip (o-skip (o-succ o-zero))) == 2
--                      ^                         ^
_ = refl

-- but we can also do the opposite!
-- if we can get a value for every 1 <S= n, then we effectively know all the elements of a vector
vTabulate : {A : Set} (n : Nat) -> (1 <S= n -> A) -> Vec A n
vTabulate zero f = []
vTabulate (suc n) f = f (o-succ (0<S= n)) ,- vTabulate n (\p -> f (o-skip p))

-- tabulating projections should result in the original vector
-- "evaluate more pls agda" might be useful here
-- reminder:
-- spacemacs - <SPC> u <SPC> u <normal-bind>
-- vscode - (should be) C-u C-u <normal-bind>
vTabulate-vProject : {A : Set} {n : Nat} -> (xs : Vec A n) -> vTabulate n (vProject xs) == xs
vTabulate-vProject [] = refl
vTabulate-vProject (x ,- xs) rewrite vTabulate-vProject xs = refl

-- projecting a tabulation should result in the original tabulation
-- again, "evaluate more pls" might be useful
-- uniqueness for 0<S= might also be useful
vProject-vTabulate :
  {A : Set} {n : Nat}
  (f : 1 <S= n -> A) (i : 1 <S= n) ->
  vProject (vTabulate n f) i == f i
vProject-vTabulate f (o-skip i) = vProject-vTabulate (\p -> f (o-skip p)) i
vProject-vTabulate f (o-succ i) rewrite 0<S=-unique i = refl
