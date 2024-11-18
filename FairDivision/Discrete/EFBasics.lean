import Mathlib

import FairDivision.Discrete.Allocations

namespace DiscreteFairDivision

variable {Agents Goods : Type}
variable [Fintype Agents] [Fintype Goods]
variable [DecidableEq Agents]
variable [DecidableEq Goods]
variable (alloc : @Alloc Agents Goods _)


/--
An allocation is Envy-Free for agent `a` w.r.t agent `b` if
`a` values their own allocation equal to or more than `a` values the allocation of `b`
-/
def EF_agents (a b : Agents) : Prop :=
      Value[alloc: a] Goodset[alloc: a] ≥ Value[alloc: a] Goodset[alloc: b]



/--
An allocation is envy-free if it is envy-free for all agents w.r.t every other agents.
The equality case is handled by the fact that each agent is trivially envy-free
w.r.t itself.
-/
def EF : Prop :=
    ∀ (a b : Agents), EF_agents alloc a b


def EF1_agents (a b : Agents) : Prop :=
     isEmpty alloc b ∨ (∃ g ∈ alloc.assign b,
        Value[alloc : a] Goodset[alloc: a] ≥ Value[alloc : a] (Goodset[alloc: b].erase g))

def EF1 : Prop :=
    ∀ (a b : Agents), EF1_agents alloc a b

def EFX_agents (a b : Agents) : Prop :=
    ∀ g ∈ alloc.assign b,
      Value[alloc: a] (alloc.assign a) ≥ Value[alloc: a] ((alloc.assign b).erase g)

def EFX : Prop :=
    ∀ (a b : Agents), EFX_agents alloc a b

omit [Fintype Agents] [Fintype Goods] [DecidableEq Agents] in
lemma empty_alloc_is_EF : isEmptyAlloc alloc → EF alloc := by
  simp [isEmptyAlloc, EF, EF_agents]
  intro hempty a b
  have ha := hempty a
  have hb := hempty b
  rw [ha, hb]

 omit [Fintype Agents] [Fintype Goods] [DecidableEq Agents] in
lemma EF_implies_EFX :
  EF alloc → EFX alloc := by
  intro hEF
  unfold EFX EFX_agents
  intro a b g g_alloc_b
  unfold EF EF_agents at hEF
  specialize hEF a b
  trans Value[alloc: a] Goodset[alloc : b]
  exact hEF
  simp[Finset.erase_subset, (Alloc[alloc : a]).mono]
omit [Fintype Agents] [Fintype Goods] [DecidableEq Agents] in
lemma EFX_implies_EF1 :
  EFX alloc → EF1 alloc := by
  intro hEFX
  simp_all [EFX, EFX_agents, EF1, EF1_agents]
  intro a b
  by_cases h : isEmpty alloc b <;> simp [h]
  simp [isEmpty] at h
  specialize hEFX a b
  apply Finset.nonempty_iff_ne_empty.mpr at h
  apply Finset.Nonempty.exists_mem at h
  cases h with
  | intro g h =>
      use g
      constructor
      exact h
      specialize hEFX g h
      exact hEFX

omit [Fintype Agents] [Fintype Goods] [DecidableEq Agents] in
lemma EF_implies_EF1 :
  EF alloc → EF1 alloc:= by
  solve_by_elim [EF_implies_EFX, EFX_implies_EF1]
end DiscreteFairDivision
