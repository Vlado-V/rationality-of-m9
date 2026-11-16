module

public import M9StacksIntegration.LagrangianCommonKernelSpan
public import M9StacksIntegration.LagrangianPluckerQuotient
public import M9StacksIntegration.LagrangianUniversalSections

/-!
# A genuine common kernel bounds the original primitive section image

The original primitive sections are the literal projection-matrix linear
combinations of the twenty native minor sections. When the original
quotient kills the first standard section, every minor containing it is
zero. The remaining projection-matrix columns lie in the actual fixed
five-dimensional subspace proved in `LagrangianCommonKernelSpan`.

This argument takes place in actual global sections and actual native H0.
It uses no field-valued-points detection or assumed primitive span bound.
Transport of an arbitrary nonzero kernel vector is a separate obligation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators

universe u

namespace M9Native.LagrangianKernelPrimitiveSections

open LagrangianField LagrangianCommonKernelSpan
open LagrangianMatrixChart LagrangianPluckerQuotient LagrangianDeterminantSections

variable (k : Type u) [Field k]

/-- The actual native primitive projection column for an original ordered minor. -/
def projectionColumn (i : Fin 20) : Fin 14 → k := fun j => projectionMatrix k j i

/-- The actual inverse coordinates on the fixed five-dimensional subspace. -/
def fiveExtraction : (Fin 14 → k) →ₗ[k] (Fin 5 → k) :=
  (LagrangianCommonKernelSpan.extraction k).comp (coordinateBasis14 k).equivFun.symm.toLinearMap

theorem fiveExtraction_embedding (v : Fin 5 → k) :
    fiveExtraction k (embeddingFourteen k v) = v := by
  simp only [fiveExtraction, embeddingFourteen, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  exact extraction_embedding k v

/-- A column whose native minor avoids the first vector lies in the
literal original five-dimensional primitive-coordinate subspace. -/
theorem projectionColumn_mem_range (i : Fin 20)
    (hi : ∀ a : Fin 3, LagrangianRing.triple i a ≠ 0) :
    projectionColumn k i ∈ LinearMap.range (embeddingFourteen k) := by
  let M : Matrix (Fin 3) (Fin 6) k := fun a => basisVector k (LagrangianRing.triple i a)
  have hM (a : Fin 3) : M a 0 = 0 := by
    simp [M, basisVector, Ne.symm (hi a)]
  have hw : rowPlucker k M = thirdBasis20 k i := by
    rw [← LagrangianRing.thirdBasis20_eq_field, LagrangianRing.thirdBasis20_apply]
    change exteriorPower.ιMulti k 3 ![M 0, M 1, M 2] = _
    congr 1
    funext a
    fin_cases a <;> rfl
  have hc : rowFourteen k M = projectionColumn k i := by
    rw [rowFourteen, hw]
    funext j
    simp only [projectionColumn, projectionMatrix, LinearMap.toMatrix_apply,
      Basis.equivFun_apply]
  rw [← hc]
  exact rowFourteen_mem_range k M hM

theorem embedding_fiveExtraction_column (i : Fin 20)
    (hi : ∀ a : Fin 3, LagrangianRing.triple i a ≠ 0) :
    embeddingFourteen k (fiveExtraction k (projectionColumn k i)) = projectionColumn k i := by
  obtain ⟨v, hv⟩ := projectionColumn_mem_range k i hi
  rw [← hv, fiveExtraction_embedding]

section LinearCombinations

variable {T : Type*} [AddCommGroup T] [Module k T]

/-- The actual original fourteen projection-matrix combinations. -/
def projectedValues (s : Fin 20 → T) (j : Fin 14) : T :=
  ∑ i : Fin 20, projectionMatrix k j i • s i

/-- Five actual linear combinations which span those primitive values
when the original first-coordinate minors vanish. -/
def fiveValues (s : Fin 20 → T) (a : Fin 5) : T :=
  ∑ i : Fin 20, fiveExtraction k (projectionColumn k i) a • s i

theorem projectedValues_expansion (s : Fin 20 → T)
    (hs : ∀ i : Fin 20, (∃ a : Fin 3, LagrangianRing.triple i a = 0) → s i = 0)
    (j : Fin 14) :
    projectedValues k s j = ∑ a : Fin 5,
      embeddingFourteen k (Pi.single a 1) j • fiveValues k s a := by
  classical
  have hcol (i : Fin 20) : projectionMatrix k j i • s i =
      ∑ a : Fin 5, (embeddingFourteen k (Pi.single a 1) j *
        fiveExtraction k (projectionColumn k i) a) • s i := by
    by_cases hi : ∃ a : Fin 3, LagrangianRing.triple i a = 0
    · simp [hs i hi]
    · have hz : ∀ a : Fin 3, LagrangianRing.triple i a ≠ 0 := by simpa using hi
      have h := congrFun (embedding_fiveExtraction_column k i hz) j
      change embeddingFourteen k (fiveExtraction k (projectionColumn k i)) j =
        projectionMatrix k j i at h
      have hv := (Pi.basisFun k (Fin 5)).sum_repr (fiveExtraction k (projectionColumn k i))
      have he := congrFun (congrArg (embeddingFourteen k) hv) j
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, Pi.basisFun_apply,
        Pi.basisFun_repr] at he
      rw [← h, ← he]
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro a _
      simp only [smul_eq_mul, mul_comm]
  unfold projectedValues
  simp_rw [hcol]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [fiveValues, Finset.smul_sum, smul_smul]

theorem projectedValues_mem_span_five (s : Fin 20 → T)
    (hs : ∀ i : Fin 20, (∃ a : Fin 3, LagrangianRing.triple i a = 0) → s i = 0)
    (j : Fin 14) :
    projectedValues k s j ∈ Submodule.span k (Set.range (fiveValues k s)) := by
  rw [projectedValues_expansion k s hs j]
  exact Submodule.sum_mem _ (fun a _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self a)))

theorem finrank_span_projectedValues_le_five (s : Fin 20 → T)
    (hs : ∀ i : Fin 20, (∃ a : Fin 3, LagrangianRing.triple i a = 0) → s i = 0) :
    finrank k (Submodule.span k (Set.range (projectedValues k s))) ≤ 5 := by
  letI : Module.Finite k (Submodule.span k (Set.range (fiveValues k s))) :=
    Module.Finite.span_of_finite k (Set.finite_range (fiveValues k s))
  have hle : Submodule.span k (Set.range (projectedValues k s)) ≤
      Submodule.span k (Set.range (fiveValues k s)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact projectedValues_mem_span_five k s hs j
  exact (Submodule.finrank_mono hle).trans (by
    simpa only [Set.finrank, Fintype.card_fin] using
      (finrank_range_le_card (R := k) (fiveValues k s)))

end LinearCombinations

section ActualSections

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {Q : X.Modules}
  (q : freeOn X 6 ⟶ Q)

/-- Original native minor sections, in actual cohomology and its original scalar action. -/
def minorH0 (i : Fin 20) : cohomologyOverField k f (Scheme.Modules.exteriorPower Q 3) 0 :=
  (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower Q 3)).inv
    (minorSection X q (LagrangianRing.triple i))

/-- The actual original primitive sections of the actual quotient, in native H0. -/
def primitiveH0 (j : Fin 14) : cohomologyOverField k f (Scheme.Modules.exteriorPower Q 3) 0 :=
  (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower Q 3)).inv
    (primitiveSection X k (ExteriorEvaluation.baseRingMap k f) q j)

theorem minorH0_eq_zero_of_first_section_zero
    (hq : q.app ⊤ (freeBasisSection X 6 0) = 0) (i : Fin 20)
    (hi : ∃ a : Fin 3, LagrangianRing.triple i a = 0) : minorH0 k f q i = 0 := by
  obtain ⟨a, ha⟩ := hi
  have hz : minorSection X q (LagrangianRing.triple i) = 0 := by
    rw [minorSection_eq_wedge]
    have h := (exteriorPower.ιMulti Γ(X,⊤) 3).map_coord_zero
      (m := fun a : Fin 3 => q.app ⊤ (freeBasisSection X 6 (LagrangianRing.triple i a))) a
      (by rw [ha, hq])
    rw [h, map_zero]
  simp only [minorH0, hz, map_zero]

theorem primitiveH0_eq_projectedValues (j : Fin 14) :
    primitiveH0 k f q j = projectedValues k (minorH0 k f q) j := by
  apply (ConcreteCategory.bijective_of_isIso
    (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower Q 3)).hom).injective
  have hscalar (a : k) (s : cohomologyOverField k f (Scheme.Modules.exteriorPower Q 3) 0) :
      (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower Q 3)).hom (a • s) =
        ExteriorEvaluation.baseRingMap k f a •
          (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower Q 3)).hom s :=
    (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower Q 3)).hom.hom.map_smul a s
  simp only [primitiveH0, projectedValues, map_sum, hscalar, minorH0, Iso.inv_hom_id_apply,
    primitiveSection]

/-- The original primitive section span has dimension at most five,
derived from a literal actual first-vector relation of the quotient. -/
theorem finrank_span_primitiveH0_le_five
    (hq : q.app ⊤ (freeBasisSection X 6 0) = 0) :
    finrank k (Submodule.span k (Set.range (primitiveH0 k f q))) ≤ 5 := by
  have h : primitiveH0 k f q = projectedValues k (minorH0 k f q) :=
    funext (primitiveH0_eq_projectedValues k f q)
  rw [h]
  exact finrank_span_projectedValues_le_five k _
    (minorH0_eq_zero_of_first_section_zero k f q hq)

end ActualSections

end M9Native.LagrangianKernelPrimitiveSections
