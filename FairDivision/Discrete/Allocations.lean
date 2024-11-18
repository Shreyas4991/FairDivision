/-
Copyright (c) 2024 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.Basic
import FairDivision.Discrete.Valuations
import FairDivision.Discrete.Valuations

namespace DiscreteFairDivision

variable {Agents Goods : Type}

variable [DecidableEq Agents]
variable [instDecEqGoods : DecidableEq Goods] -- Indivisible goods only

structure Alloc where
  assign : Agents → Finset Goods
  valuations : Agents → @Val Goods
  disjoint : ∀ a b : Agents, a ≠ b → assign a ∩ assign b = ∅


notation "Goodset[" alloc " : " agent "]" => Alloc.assign alloc agent
notation "Value[" alloc " : " agent "]" => Val.val (Alloc.valuations alloc agent)
notation "Alloc[" alloc " : " agent "]" => Alloc.valuations alloc agent
variable (alloc : @Alloc Agents Goods _)




def isEmpty (a : Agents):=
  alloc.assign a = ∅

abbrev unAllocated (g : Goods) := ∀ a, g ∉ alloc.assign a

def allocate (g : Goods) (a : Agents) (h : unAllocated alloc g): @Alloc Agents Goods _ := {
  assign := fun (x : Agents) => if x = a then (alloc.assign x) ∪ {g} else alloc.assign x

  valuations := fun agent => allZeroVal -- trivial valuation

  disjoint := by
    intro arb_a arb_b hneq
    simp
    by_cases ha : arb_a = a
    case pos =>
      have hneqb : arb_b ≠ a := by
        by_contra heqarb_a
        simp_all only [ne_eq, not_true_eq_false]
      simp [ha, hneqb, Finset.union_inter_distrib_right]
      rw [←ha, alloc.disjoint]
      simp [h]
      exact hneq
    case neg =>
      by_cases hb : arb_b = a <;>
        simp[hb, ha, alloc.disjoint, hneq]
      rw[←hb]
      simp[Finset.inter_union_distrib_left, hneq, alloc.disjoint]
      simp [h]
}

def isEmptyAlloc  :=
  ∀ a : Agents, alloc.assign a = ∅




/-- An  allocation is complete if all goods are allocated to some agent-/
def complete : Prop :=
  ∀ g : Goods, ∃ a : Agents, g ∈ alloc.assign a

open BigOperators

omit [DecidableEq Agents] in
lemma complete_union
  (h_complete : @complete Agents Goods _ alloc) : ∀ g : Goods, g ∈ ⋃ a : Agents, Goodset[alloc : a].toSet := by
  intro g
  unfold complete at h_complete
  specialize h_complete g
  simp
  assumption

end DiscreteFairDivision
