module

public import M9StacksIntegration.SplitQuadricQuotientCoordinates

/-!
# Every finite linear section of the actual split quadric has length at most two

The only geometric hypothesis is actual finiteness over the original
field. A quotient basis is chosen inside the proof. Neither its rank,
a matrix frame, reducedness nor a length bound is supplied. The actual
inverse-image ideal and all nilpotents are retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open AlgebraicGeometry.ProjectiveSpaceOfModule
open M9Native.SplitQuadricLinearSection
universe u

namespace M9Native.SplitQuadricFiniteLinearSection
variable (K : Type u) [Field K]

private theorem empty_projective_of_subsingleton (W : Submodule K (coordinates K))
    [Subsingleton (coordinates K ⧸ W)] : IsEmpty (linearProjective K W) := by
  refine ⟨fun p => ?_⟩
  obtain ⟨v,hv⟩ := exists_ι_notMem K (coordinates K ⧸ W) p
  apply hv
  rw [Subsingleton.elim v 0, map_zero]
  exact zero_mem _

private theorem empty_section_h0 (W : Submodule K (coordinates K))
    [Subsingleton (coordinates K ⧸ W)] :
    Module.finrank K (structureSheafCohomology (sectionProjection K W) 0) = 0 := by
  let : IsEmpty (linearProjective K W) := empty_projective_of_subsingleton K W
  let : IsEmpty (linearSection K W) := ⟨fun z => isEmptyElim (toLinear K W z)⟩
  let : Subsingleton Γ(SheafOfModules.unit (linearSection K W).ringCatSheaf, ⊤) := by
    change Subsingleton Γ(linearSection K W, ⊤)
    infer_instance
  let : Subsingleton (cohomologyOverField K (sectionProjection K W)
      (SheafOfModules.unit (linearSection K W).ringCatSheaf) 0) :=
    (cohomologyOverFieldZeroEquivSections K (sectionProjection K W)
      (SheafOfModules.unit (linearSection K W).ringCatSheaf)).subsingleton
  let : Subsingleton (structureSheafCohomology (sectionProjection K W) 0) :=
    (structureSheafCohomologyIsoCohomologyOverField K (sectionProjection K W) 0).toLinearEquiv.toEquiv.subsingleton
  exact Module.finrank_zero_of_subsingleton

/-- Both the ambient point/line restriction and the full scheme length bound
follow from true finiteness of the original linear-section scheme. -/
theorem finite_section_bounds (W : Submodule K (coordinates K))
    [IsFinite (sectionProjection K W)] :
    Module.finrank K (coordinates K ⧸ W) ≤ 2 ∧
      Module.finrank K (structureSheafCohomology (sectionProjection K W) 0) ≤ 2 := by
  by_cases h0 : Module.finrank K (coordinates K ⧸ W) = 0
  · let : Subsingleton (coordinates K ⧸ W) := Module.finrank_zero_iff.mp h0
    exact ⟨by omega, (empty_section_h0 K W).le.trans (by omega)⟩
  · let n := Module.finrank K (coordinates K ⧸ W) - 1
    have hn : Module.finrank K (coordinates K ⧸ W) = n+1 := by omega
    let b := Module.finBasisOfFinrankEq K (coordinates K ⧸ W) hn
    let ψ := SplitQuadricQuotientCoordinates.gradedMap K W n b
    have hψ : Function.Surjective ψ := SplitQuadricQuotientCoordinates.gradedMap_surjective K W n b
    let e := SplitQuadricQuotientCoordinates.sectionIso K W n b
    let pY := ProjectiveQuadricLinearPullback.sectionProjection K n ψ hψ
    have he : e.hom ≫ pY = sectionProjection K W :=
      SplitQuadricQuotientCoordinates.sectionIso_over K W n b
    let : IsFinite pY := SplitQuadricQuotientCoordinates.finite_target_of_iso
      K e (sectionProjection K W) pY he
    have hK : ∀ c : K, ψ (MvPolynomial.C c) = MvPolynomial.C c :=
      SplitQuadricQuotientCoordinates.gradedMap_C K W n b
    have hdim := ProjectiveQuadricLinearPullback.ambient_le_one_of_finite K n ψ hψ hK
    have hlen := ProjectiveQuadricLinearPullback.finite_section_h0_le_two K n ψ hψ hK
    have hcoh := (SplitQuadricQuotientCoordinates.structureCohomologyIso K e
      (sectionProjection K W) pY he 0).toLinearEquiv.finrank_eq
    exact ⟨by omega, hcoh.trans_le hlen⟩

theorem quotient_finrank_le_two (W : Submodule K (coordinates K))
    [IsFinite (sectionProjection K W)] : Module.finrank K (coordinates K ⧸ W) ≤ 2 :=
  (finite_section_bounds K W).1

/-- Native original-field H0 counts the full finite scheme, including double points. -/
theorem finite_section_h0_le_two (W : Submodule K (coordinates K))
    [IsFinite (sectionProjection K W)] :
    Module.finrank K (structureSheafCohomology (sectionProjection K W) 0) ≤ 2 :=
  (finite_section_bounds K W).2

end M9Native.SplitQuadricFiniteLinearSection
