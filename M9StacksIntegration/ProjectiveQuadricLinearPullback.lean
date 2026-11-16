module

public import M9StacksIntegration.SplitQuadricLinearSection
public import M9StacksIntegration.ProjectiveQuadraticDimension
public import StacksFrontier.AlgebraicGeometry.ProjMapTwistDegreeSection.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence

/-!
# Actual quadratic pullback along a projective linear quotient

The original quadratic zero ideal, not its radical, pulls back to the
actual image quadratic under the graded quotient. The original structural
coefficient map is checked explicitly. Finiteness then derives both the
ambient point/line restriction and the H0 length bound, without supplying
either as a premise.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection
open M9Native.ProjectiveQuadraticCohomology M9Native.ProjectiveQuadraticDimension
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace M9Native.ProjectiveQuadricLinearPullback
variable (K : Type u) [Field K] (n : ℕ)
variable (ψ : polyGrading K 4 →+*ᵍ polyGrading K n) (hψ : Function.Surjective ψ)

def linearMap : projective K n ⟶ SplitQuadricLinearSection.ambient K :=
  Proj.map ψ (Proj.irrelevant_le_map_of_surjective ψ hψ)

instance linearMap_closed : IsClosedImmersion (linearMap K n ψ hψ) :=
  Proj.isClosedImmersion_map_of_surjective' ψ hψ

theorem coefficientZeroHom_eq (m : ℕ) :
    (GradedRing.projZeroRingHom' (polyGrading K m)).comp
        (algebraMap K (MvPolynomial (Fin (m+1)) K)) = algebraMap K (polyGrading K m 0) := by
  apply RingHom.ext
  intro c
  have h := GradedRing.projZeroRingHom'_apply_coe (polyGrading K m)
    (algebraMap K (polyGrading K m 0) c)
  simpa only [RingHom.comp_apply, SetLike.GradeZero.coe_algebraMap] using h

/-- The scalar triangle follows from the actual graded map on the original coefficients. -/
theorem linearMap_over (hK : ∀ c : K, ψ (MvPolynomial.C c) = MvPolynomial.C c) :
    linearMap K n ψ hψ ≫ projToSpecCoeff K 4 = projToSpecCoeff K n := by
  have h0 : ψ.gradedZeroRingHom.comp (algebraMap K (polyGrading K 4 0)) =
      algebraMap K (polyGrading K n 0) := by
    apply RingHom.ext
    intro c
    apply Subtype.ext
    exact hK c
  dsimp only [linearMap]
  rw [projToSpecCoeff, projToSpecCoeff, coefficientZeroHom_eq, coefficientZeroHom_eq,
    ← Category.assoc, Proj.map_toSpecZero, Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, h0]

def restrictedForm : polyGrading K n 2 :=
  ⟨ψ (SplitQuadricLinearSection.form K), ψ.map_mem (SplitQuadricLinearSection.form K).property⟩

abbrev sectionIdeal := (SplitQuadricLinearSection.quadricIdeal K).comap (linearMap K n ψ hψ)
abbrev sectionScheme : Scheme.{u} := (sectionIdeal K n ψ hψ).subscheme
abbrev sectionProjection : sectionScheme K n ψ hψ ⟶ Spec (.of K) :=
  (sectionIdeal K n ψ hψ).subschemeι ≫ linearMap K n ψ hψ ≫ projToSpecCoeff K 4

private theorem pullbackGlobal_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (s : Γ(M, ⊤)) : pullbackGlobalSections f M s =
      Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection f M s := by
  change ((Scheme.Modules.pullback f).obj M).presheaf.map
      (eqToHom (show f ⁻¹ᵁ (⊤ : Y.Opens) = ⊤ from rfl)).op
      (Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection f M s) = _
  exact Functor.map_id_apply _ _ _

/-- Exact original ideal equality, retaining all nilpotents. -/
theorem sectionIdeal_eq : sectionIdeal K n ψ hψ =
    quadraticIdeal K n (polynomialSection K n (restrictedForm K n ψ)) := by
  rw [sectionIdeal, SplitQuadricLinearSection.quadricIdeal_eq,
    ← Stacks.Divisors.zeroScheme_pullback]
  dsimp only [quadraticIdeal]
  rw [polynomialSection_eval]
  apply zeroScheme_eq_of_iso
    (pullbackTwistIso ψ (Proj.irrelevant_le_map_of_surjective ψ hψ) hψ
      (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin 5) K) 2)
  rw [pullbackGlobal_eq]
  exact pullbackTwistIso_degreeSection ψ (Proj.irrelevant_le_map_of_surjective ψ hψ) hψ
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin 5) K) 2
    (SplitQuadricLinearSection.form K)

theorem sectionProjection_eq (hK : ∀ c : K, ψ (MvPolynomial.C c) = MvPolynomial.C c) :
    sectionProjection K n ψ hψ = (sectionIdeal K n ψ hψ).subschemeι ≫ projToSpecCoeff K n := by
  rw [sectionProjection, linearMap_over K n ψ hψ hK]

/-- The finiteness of the actual inverse-image scheme forces its linear ambient dimension. -/
theorem ambient_le_one_of_finite
    (hK : ∀ c : K, ψ (MvPolynomial.C c) = MvPolynomial.C c)
    [IsFinite (sectionProjection K n ψ hψ)] : n ≤ 1 := by
  let : IsFinite (quadraticProjection K n (polynomialSection K n (restrictedForm K n ψ))) := by
    change IsFinite ((quadraticIdeal K n (polynomialSection K n (restrictedForm K n ψ))).subschemeι ≫
      projToSpecCoeff K n)
    rw [← sectionIdeal_eq K n ψ hψ, ← sectionProjection_eq K n ψ hψ hK]
    infer_instance
  exact ProjectiveQuadraticDimension.ambient_le_one_of_finite K n (restrictedForm K n ψ)

/-- The genuine finite linear-section length bound; no point/line/rank premise is supplied. -/
theorem finite_section_h0_le_two
    (hK : ∀ c : K, ψ (MvPolynomial.C c) = MvPolynomial.C c)
    [IsFinite (sectionProjection K n ψ hψ)] :
    Module.finrank K (structureSheafCohomology (sectionProjection K n ψ hψ) 0) ≤ 2 := by
  let : IsFinite (quadraticProjection K n (polynomialSection K n (restrictedForm K n ψ))) := by
    change IsFinite ((quadraticIdeal K n (polynomialSection K n (restrictedForm K n ψ))).subschemeι ≫
      projToSpecCoeff K n)
    rw [← sectionIdeal_eq K n ψ hψ, ← sectionProjection_eq K n ψ hψ hK]
    infer_instance
  rw [sectionProjection_eq K n ψ hψ hK]
  change Module.finrank K (structureSheafCohomology
    (X := (sectionIdeal K n ψ hψ).subscheme)
    ((sectionIdeal K n ψ hψ).subschemeι ≫ projToSpecCoeff K n) 0) ≤ 2
  rw [sectionIdeal_eq K n ψ hψ]
  exact finite_quadratic_h0_le_two K n (polynomialSection K n (restrictedForm K n ψ))

end M9Native.ProjectiveQuadricLinearPullback
