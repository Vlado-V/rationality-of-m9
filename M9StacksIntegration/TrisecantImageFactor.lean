module

public import M9StacksIntegration.MixedQuadraticTrisecant
public import M9StacksIntegration.ClosedProjectiveLineInCurve

/-! Full closed divisor images on an actual projective line.
Their native structural H0 is preserved by the genuine closed-image
isomorphism. Mixed linear/quadratic ideals then contradict a positive
genus original curve, with every nilpotent retained. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open M9Native.ProjectiveQuadraticCohomology M9Native.ProjectiveQuadraticDimension
universe u

namespace M9Native.TrisecantImageFactor

variable (K : Type u) [Field K]

/-- The actual full scheme-theoretic closed image has the same original
field structural H0 as its source. No reduced-image replacement. -/
theorem image_h0_eq {T : Scheme.{u}} (qT : T ⟶ Spec (.of K))
    (t : T ⟶ projective K 1) [IsClosedImmersion t]
    (ht : t ≫ projToSpecCoeff K 1 = qT) :
    Module.finrank K (structureSheafCohomology
      (t.ker.subschemeι ≫ projToSpecCoeff K 1) 0) =
        Module.finrank K (structureSheafCohomology qT 0) := by
  let p := t.ker.subschemeι ≫ projToSpecCoeff K 1
  have hbase : t.toImage ≫ p = qT := by
    change t.toImage ≫ (t.ker.subschemeι ≫ projToSpecCoeff K 1) = qT
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    exact ht
  calc
    Module.finrank K (structureSheafCohomology p 0) =
        Module.finrank K (cohomologyOverField K p
          (SheafOfModules.unit t.image.ringCatSheaf) 0) :=
      (structureSheafCohomologyIsoCohomologyOverField K p 0).toLinearEquiv.finrank_eq
    _ = Module.finrank K (cohomologyOverField K (t.toImage ≫ p)
          (SheafOfModules.unit T.ringCatSheaf) 0) :=
      (finrank_cohomologyOverField_unit_pushforward K t.toImage p 0).symm
    _ = Module.finrank K (cohomologyOverField K qT
          (SheafOfModules.unit T.ringCatSheaf) 0) := by rw [hbase]
    _ = Module.finrank K (structureSheafCohomology qT 0) :=
      (structureSheafCohomologyIsoCohomologyOverField K qT 0).toLinearEquiv.finrank_eq.symm

/-- The ambient original curve ideal restricts to an ideal vanishing on
the FULL closed line-image divisor. -/
theorem curveIdeal_comap_le_image {X T : Scheme.{u}} {n : ℕ}
    (κ : X ⟶ projective K n) (i : T ⟶ X) (t : T ⟶ projective K 1)
    (l : projective K 1 ⟶ projective K n) (h : t ≫ l = i ≫ κ) :
    κ.ker.comap l ≤ t.ker := by
  apply (Scheme.IdealSheafData.le_map_iff_comap_le).mp
  rw [Scheme.IdealSheafData.map_ker, h]
  exact Scheme.Hom.le_ker_comp i κ

/-- A literal mixed-degree ideal defining the ORIGINAL embedded curve
excludes every actual closed length-at-least-three divisor factoring
through a genuine projective line. -/
theorem no_mixed_trisecant {X T : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsCurve K f]
    {n : ℕ} (κ : X ⟶ projective K n) [IsClosedImmersion κ]
    (hκ : κ ≫ projToSpecCoeff K n = f) (hgenus : genus f ≠ 0)
    {ι κq : Type u} (F : ι → polyGrading K n 1) (Q : κq → polyGrading K n 2)
    (hI : κ.ker = (⨆a, MixedQuadraticTrisecant.degreeIdeal K n 1 (F a)) ⊔
      (⨆b, quadraticIdeal K n (polynomialSection K n (Q b))))
    (i : T ⟶ X) [IsClosedImmersion i]
    (hD : 3 ≤ Module.finrank K (structureSheafCohomology (i ≫ f) 0))
    (ψ : polyGrading K n →+*ᵍ polyGrading K 1) (hψ : Function.Surjective ψ)
    (hl : QuadraticTrisecant.linearMap K n ψ hψ ≫ projToSpecCoeff K n = projToSpecCoeff K 1)
    (t : T ⟶ projective K 1) (htbase : t ≫ projToSpecCoeff K 1 = i ≫ f)
    (ht : t ≫ QuadraticTrisecant.linearMap K n ψ hψ = i ≫ κ) : False := by
  let l := QuadraticTrisecant.linearMap K n ψ hψ
  letI : IsClosedImmersion (t ≫ l) := ht.symm ▸ inferInstance
  letI : IsClosedImmersion t := IsClosedImmersion.of_comp_isClosedImmersion t l
  have hlen : 3 ≤ Module.finrank K (structureSheafCohomology
      (t.ker.subschemeι ≫ projToSpecCoeff K 1) 0) := by
    rw [image_h0_eq K (i ≫ f) t htbase]
    exact hD
  have hvan := curveIdeal_comap_le_image K κ i t l ht
  have hz := MixedQuadraticTrisecant.mixed_generated_comap_eq_bot K n ψ hψ
    F Q κ.ker hI t.ker hlen hvan
  have hle : κ.ker ≤ l.ker := by
    rw [← Scheme.IdealSheafData.map_bot l]
    exact (Scheme.IdealSheafData.le_map_iff_comap_le).mpr (by rw [hz])
  obtain ⟨u, hu⟩ := (factorsThrough_ideal_iff_ideal_le_ker κ.ker l).mpr hle
  have hinv : inv κ.toImage ≫ κ = κ.imageι := by
    apply (cancel_epi κ.toImage).1
    simp only [IsIso.hom_inv_id_assoc, Scheme.Hom.toImage_imageι]
  have hfactor : (u ≫ inv κ.toImage) ≫ κ = l := by
    rw [Category.assoc, hinv]
    exact hu
  exact ClosedProjectiveLineInCurve.no_line_factor K f (projToSpecCoeff K n)
    κ hκ l hl hgenus ⟨u ≫ inv κ.toImage, hfactor⟩

end M9Native.TrisecantImageFactor
