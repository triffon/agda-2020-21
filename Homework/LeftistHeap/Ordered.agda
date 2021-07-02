{-# OPTIONS --no-unicode #-}

module Homework.LeftistHeap.Ordered where

open import Lib.Sum
open import Lib.One
open import Homework.LeftistHeap.Common
open import Lib.Nat

-- parametrised by the lower bound of the heap
data Heap (lower : Priority) : Set where
  empty : Heap lower
  node : Rank -> (p : Priority) -> Leq lower p -> Heap lower -> Heap lower -> Heap lower

-- note how the left empty has a lower rank than the right node
wrongRankprop : Heap 0
wrongRankprop = node 2 0 <> empty (node 1 5 <> empty empty)

-- note how the rank assigned here is just wrong
wrongRank : Heap 0
wrongRank = node 1337 0 <> empty empty

-- for the ordering
-- 1 <= 2
-- 1 <= 3
-- also, the ranks are correct, since 3 = 1 + (1 + 1)
-- and the rank property is preserved, since
-- 1 (rank of the right tree) <= 1 (rank of the left tree)
proper : Heap 1
proper = node 3 1 <> (node 1 2 <> empty empty) (node 1 3 <> empty empty)

rank : {lower : Priority} -> Heap lower -> Rank
rank empty = 0
rank (node r _ _ _ _) = r

mkNode :
  {lower : Priority} (x : Priority) ->
  Leq lower x -> Heap x -> Heap x -> Heap lower
mkNode x lower<=x h1 h2 with decLeq (rank h1) (rank h2)
... | inl r1<=r2
  = node (suc (rank h2 +N rank h1)) x lower<=x h2 h1
... | inr r2<=r1
  = node (suc (rank h1 +N rank h2)) x lower<=x h1 (Leq-refl x) h2 (Leq-refl x)

{-# TERMINATING #-}
merge :
  {lower : Priority} ->
  Heap lower -> Heap lower -> Heap lower
merge empty h2 = h2
merge h1 empty = h1
merge h1@(node rk1 p1 lower<=p1 l1 _ r1 _)
      h2@(node rk2 p2 lower<=p2 l2 _ r2 _) with decLeq p1 p2
... | inl p1<=p2 = mkNode p1 lower<=p1 l1 (merge r1 h2)
... | inr p2<=p1 = mkNode p2 lower<=p2 l2 (merge r2 h1)

singleton : {lower : Priority} (x : Priority) -> Leq lower x -> Heap lower
singleton = {!!}

weakenHeap : (n m : Priority) -> Leq n m -> Heap {!!} -> Heap {!!}
weakenHeap = {!!}

insert : {lower : Priority} (x : Priority) -> Heap lower -> Heap {!!}
insert = {!!}

findMin : {lower : Priority} -> Heap lower -> Maybe Priority
findMin = {!!}

delMin : {lower : Priority} -> Heap lower -> Maybe (Heap lower)
delMin = {!!}
