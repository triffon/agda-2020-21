{-# OPTIONS --no-unicode #-}

module Homework.LeftistHeap.Ordered where

open import Lib.Sum
open import Lib.One
open import Homework.LeftistHeap.Common
open import Lib.Nat

-- parametrised by the lower bound of the heap
data Heap (lower : Priority) : Set where
  empty : Heap lower
  node : Rank -> (p : Priority) -> Leq lower p -> {llower : Priority} -> Heap llower -> Leq p llower -> {rlower : Priority} -> Heap rlower -> Leq p rlower -> Heap lower

-- note how the left empty has a lower rank than the right node
wrongRankprop : Heap 0
wrongRankprop = node 2 0 <> {0} empty <> {5} (node 1 5 <> {5} empty <> {5} empty <>) <>

-- note how the rank assigned here is just wrong
wrongRank : Heap 0
wrongRank = node 1337 0 <> {0} empty <> {0} empty <>

-- for the ordering
-- 1 <= 2
-- 1 <= 3
-- also, the ranks are correct, since 3 = 1 + (1 + 1)
-- and the rank property is preserved, since
-- 1 (rank of the right tree) <= 1 (rank of the left tree)
proper : Heap 1
proper = node 3 1 <> {2} (node 1 2 <> {2} empty <> {2} empty <>) <> {3} (node 1 3 <> {3} empty <> {3} empty <>) <>

rank : {lower : Priority} -> Heap lower -> Rank
rank empty = 0
rank (node r _ _ _ _ _ _) = r

mkNode :
  {lower : Priority} (x : Priority) ->
  Leq lower x -> Heap x -> Heap x -> Heap lower
mkNode x lower<=x h1 h2 with decLeq (rank h1) (rank h2)
... | inl r1<=r2 = node (suc (rank h2 +N rank h1)) x lower<=x h2 (Leq-refl x) h1 (Leq-refl x)
... | inr r2<=r1 = node (suc (rank h1 +N rank h2)) x lower<=x h1 (Leq-refl x) h2 (Leq-refl x)

{-# TERMINATING #-}
merge :
  {lower : Priority} ->
  Heap lower -> Heap lower -> Heap lower
merge = {!!}

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
