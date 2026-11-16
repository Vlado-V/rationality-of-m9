module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Fin.Embedding

/-! Literal first rows of an actual surjective five-by-fourteen matrix.
The list-prefix and finite-index conventions are identified explicitly. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open Module Matrix

universe u

namespace M9Native.LagrangianRowPrefixes

variable (K : Type u) [Field K] (M : Matrix (Fin 5) (Fin 14) K)

def headRows (i : ℕ) (hi : i ≤ 5) : Fin i → (Fin 14 → K) :=
  fun j => M (Fin.castLE hi j)

omit [Field K] in
theorem ofFn_headRows (i : ℕ) (hi : i ≤ 5) :
    List.ofFn (headRows K M i hi) = (List.ofFn M).take i := by
  apply List.ext_getElem
  · simpa only [List.length_ofFn,List.length_take] using (Nat.min_eq_left hi).symm
  · intro j hj hj'
    simp only [List.getElem_ofFn,List.getElem_take]
    rfl

omit [Field K] in
theorem range_headRows (i : ℕ) (hi : i ≤ 5) :
    Set.range (headRows K M i hi) =
      {v : Fin 14 → K | v ∈ (List.ofFn M).take i} := by
  rw [← ofFn_headRows K M i hi]
  ext v
  simp only [Set.mem_range,Set.mem_ofPred_eq,List.mem_ofFn]

theorem rows_linearIndependent (hM : Function.Surjective M.mulVec) :
    LinearIndependent K M.row := by
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  change Fintype.card (Fin 5) = finrank K (Submodule.span K (Set.range M.row))
  exact ((Matrix.mulVec_surjective_iff_rank_eq_card (M := M)).mp hM).symm.trans
    (Matrix.rank_eq_finrank_span_row M)

theorem headRows_linearIndependent (hM : Function.Surjective M.mulVec)
    (i : ℕ) (hi : i ≤ 5) : LinearIndependent K (headRows K M i hi) :=
  (rows_linearIndependent K M hM).comp (Fin.castLE hi) (Fin.castLE_injective hi)

theorem headRows_snoc_linearIndependent (hM : Function.Surjective M.mulVec)
    (i : ℕ) (hi : i < 5) :
    LinearIndependent K
      (Fin.snoc (headRows K M i (Nat.le_of_lt hi)) (M ⟨i,hi⟩)) := by
  have hcast : i+1 ≤ 5 := hi
  have he : Fin.snoc (headRows K M i (Nat.le_of_lt hi)) (M ⟨i,hi⟩) =
      M.row ∘ Fin.castLE hcast := by
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · rw [Fin.snoc_last]
      rfl
    · rw [Fin.snoc_castSucc]
      rfl
  rw [he]
  exact (rows_linearIndependent K M hM).comp (Fin.castLE hcast) (Fin.castLE_injective hcast)

theorem next_notMem_span_headRows (hM : Function.Surjective M.mulVec)
    (i : ℕ) (hi : i < 5) :
    M ⟨i,hi⟩ ∉ Submodule.span K (Set.range (headRows K M i (Nat.le_of_lt hi))) :=
  (linearIndependent_finSnoc.mp (headRows_snoc_linearIndependent K M hM i hi)).2

end M9Native.LagrangianRowPrefixes
end
