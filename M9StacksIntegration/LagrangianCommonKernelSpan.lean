module

public import M9StacksIntegration.LagrangianGrassmannian
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# The original primitive span when a quotient kills the first vector

The original coordinates are (a,q,p,b), with both matrices symmetric.
If the original six-column quotient has zero first column, then a=0,
the first row/column of q is zero, and p has only its (0,0) entry.
Thus its original primitive coordinate projection lies in an actual
five-dimensional linear subspace. No isotropy or span bound is assumed.

This is the standard-vector algebra in Mukai II Lemma4.3. Transporting
an arbitrary nonzero common kernel vector to the first vector and the
subsequent original curve restriction argument are separate obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open Module
open scoped BigOperators

universe u

namespace M9Native.LagrangianCommonKernelSpan

open LagrangianField

variable (K : Type u) [Field K]

def qBlock : (Fin 5 → K) →ₗ[K] Symmetric3 K where
  toFun v := ⟨![![0,0,0], ![0,v 0,v 1], ![0,v 1,v 2]], by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl⟩
  map_add' v w := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_smul' c v := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp

def pBlock : (Fin 5 → K) →ₗ[K] Symmetric3 K where
  toFun v := ⟨![![v 3,0,0], ![0,0,0], ![0,0,0]], by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl⟩
  map_add' v w := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_smul' c v := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp

/-- The literal five-coordinate subspace in the original (a,q,p,b) model. -/
def embedding : (Fin 5 → K) →ₗ[K] Coordinates K :=
  (0 : (Fin 5 → K) →ₗ[K] K).prod ((qBlock K).prod ((pBlock K).prod (LinearMap.proj 4)))

/-- Its actual inverse coordinates on its range. -/
def extraction : Coordinates K →ₗ[K] (Fin 5 → K) where
  toFun r := ![r.2.1.val 1 1, r.2.1.val 1 2, r.2.1.val 2 2, r.2.2.1.val 0 0, r.2.2.2]
  map_add' r s := by ext i; fin_cases i <;> rfl
  map_smul' c r := by ext i; fin_cases i <;> rfl

theorem extraction_embedding (v : Fin 5 → K) : extraction K (embedding K v) = v := by
  ext i
  fin_cases i <;> rfl

theorem embedding_injective : Function.Injective (embedding K) :=
  Function.LeftInverse.injective (extraction_embedding K)

private theorem embedding_extraction_of_constraints (r : Coordinates K)
    (ha : r.1 = 0) (hq : ∀ j : Fin 3, r.2.1.val 0 j = 0)
    (hp : ∀ i j : Fin 3, j ≠ 0 → r.2.2.1.val i j = 0) :
    embedding K (extraction K r) = r := by
  have hqSymm (i j : Fin 3) : r.2.1.val i j = r.2.1.val j i :=
    congrFun (congrFun r.2.1.property j) i
  have hpSymm (i j : Fin 3) : r.2.2.1.val i j = r.2.2.1.val j i :=
    congrFun (congrFun r.2.2.1.property j) i
  have hq0 (i : Fin 3) : r.2.1.val i 0 = 0 := (hqSymm i 0).trans (hq i)
  have hp0 (i : Fin 3) (hi : i ≠ 0) : r.2.2.1.val i 0 = 0 :=
    (hpSymm i 0).trans (hp 0 i hi)
  apply Prod.ext
  · simpa [embedding] using ha.symm
  apply Prod.ext
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [embedding, extraction, qBlock, hq, hq0, hqSymm]
  apply Prod.ext
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [embedding, extraction, pBlock, hp, hp0, hpSymm]
  · rfl

private theorem qExtraction_upper (w : Third K) (i j : Fin 3) (hij : i ≤ j) :
    (qExtraction K w).val i j = qCoordinate K i j w := by
  change upperMatrix (fun ij : Upper3 => qCoordinate K ij.val.1 ij.val.2 w) i j = _
  simp [upperMatrix, hij]

private theorem pExtraction_upper (w : Third K) (i j : Fin 3) (hij : i ≤ j) :
    (pExtraction K w).val i j = pCoordinate K i j w := by
  change upperMatrix (fun ij : Upper3 => pCoordinate K ij.val.1 ij.val.2 w) i j = _
  simp [upperMatrix, hij]

private theorem qCoordinate_first_zero (M : Matrix (Fin 3) (Fin 6) K)
    (hM : ∀ i : Fin 3, M i 0 = 0) (j : Fin 3) :
    qCoordinate K 0 j (rowPlucker K M) = 0 := by
  simp [qCoordinate, rowPlucker, coordinate_wedge3, eIndex, hM]

private theorem pCoordinate_other_zero (M : Matrix (Fin 3) (Fin 6) K)
    (hM : ∀ i : Fin 3, M i 0 = 0) (i j : Fin 3) (hj : j ≠ 0) :
    pCoordinate K i j (rowPlucker K M) = 0 := by
  fin_cases j
  · exact (hj rfl).elim
  · simp [pCoordinate, rowPlucker, coordinate_wedge3, nextOne, nextTwo, eIndex, fIndex, hM]
  · simp [pCoordinate, rowPlucker, coordinate_wedge3, nextOne, nextTwo, eIndex, fIndex, hM]

/-- Zero first column gives actual membership in the literal five-dimensional
coordinate subspace, before any isotropy condition is imposed. -/
theorem rowProjection_mem_range (M : Matrix (Fin 3) (Fin 6) K)
    (hM : ∀ i : Fin 3, M i 0 = 0) :
    coordinateProjection K (rowPlucker K M) ∈ LinearMap.range (embedding K) := by
  let r := coordinateProjection K (rowPlucker K M)
  have ha : r.1 = 0 := by
    simp [r, coordinateProjection, aCoordinate, rowPlucker, coordinate_wedge3, hM]
  have hq (j : Fin 3) : r.2.1.val 0 j = 0 :=
    (qExtraction_upper K (rowPlucker K M) 0 j (Fin.zero_le j)).trans
      (qCoordinate_first_zero K M hM j)
  have hp (i j : Fin 3) (hj : j ≠ 0) : r.2.2.1.val i j = 0 := by
    by_cases hij : i ≤ j
    · exact (pExtraction_upper K (rowPlucker K M) i j hij).trans
        (pCoordinate_other_zero K M hM i j hj)
    · have hi : i ≠ 0 := by omega
      have hs : r.2.2.1.val i j = r.2.2.1.val j i :=
        congrFun (congrFun r.2.2.1.property j) i
      exact hs.trans ((pExtraction_upper K (rowPlucker K M) j i (le_of_not_ge hij)).trans
        (pCoordinate_other_zero K M hM j i hi))
  exact ⟨extraction K r, embedding_extraction_of_constraints K r ha hq hp⟩

/-- The same actual subspace in the literal original fourteen coordinates. -/
def embeddingFourteen : (Fin 5 → K) →ₗ[K] (Fin 14 → K) :=
  (coordinateBasis14 K).equivFun.toLinearMap.comp (embedding K)

theorem finrank_range_embeddingFourteen : finrank K (LinearMap.range (embeddingFourteen K)) = 5 := by
  have hi : Function.Injective (embeddingFourteen K) :=
    (coordinateBasis14 K).equivFun.injective.comp (embedding_injective K)
  simpa using LinearMap.finrank_range_of_inj hi

theorem rowFourteen_mem_range (M : Matrix (Fin 3) (Fin 6) K)
    (hM : ∀ i : Fin 3, M i 0 = 0) :
    rowFourteen K M ∈ LinearMap.range (embeddingFourteen K) := by
  obtain ⟨v, hv⟩ := rowProjection_mem_range K M hM
  exact ⟨v, congrArg (coordinateBasis14 K).equivFun hv⟩

/-- Any family of original quotient matrices killing the original first
vector has actual primitive span of dimension at most five. -/
theorem finrank_span_rowFourteen_le_five {ι : Type*}
    (M : ι → Matrix (Fin 3) (Fin 6) K) (hM : ∀ t i, M t i 0 = 0) :
    finrank K (Submodule.span K (Set.range (fun t => rowFourteen K (M t)))) ≤ 5 := by
  have hle : Submodule.span K (Set.range (fun t => rowFourteen K (M t))) ≤
      LinearMap.range (embeddingFourteen K) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨t, rfl⟩
    exact rowFourteen_mem_range K (M t) (hM t)
  exact (Submodule.finrank_mono hle).trans_eq (finrank_range_embeddingFourteen K)

end M9Native.LagrangianCommonKernelSpan
