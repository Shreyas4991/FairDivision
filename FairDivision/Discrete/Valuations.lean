import Mathlib


namespace DiscreteFairDivision

variable {Agents Goods : Type}
variable [Fintype Agents] [Fintype Goods]
variable [DecidableEq Agents]
variable [DecidableEq Goods] -- Indivisible goods only

structure Val where
  val : Finset Goods → ℝ
  empty : val ∅ = 0
  pos : ∀ s : Finset Goods, val s ≥ 0
  mono : ∀ s t : Finset Goods,
    s ⊆ t → val s ≤ val t

variable (v : @Val Goods)

def allZeroVal : @Val Goods where
  val := fun _ => 0
  empty := by rfl
  pos := by simp
  mono := by
    intro s t s_subset_t
    dsimp
    rfl

def valSingle (g : Goods) :=
  v.val {g}

structure AdditiveVal
  extends Val where
    additive :  ∀ A B : Finset Goods,
      val (A ∪ B) = val A + val B - val (A ∩ B)

structure SubAdditiveVal
  extends Val where
    subadditive : ∀ A B : Finset Goods,
      val (A ∪ B) ≤ val A + val B - val (A ∩ B)


end DiscreteFairDivision
