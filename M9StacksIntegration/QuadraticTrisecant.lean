module

public import M9StacksIntegration.FiniteClosedSectionH0
public import M9StacksIntegration.ProjectiveQuadraticDimension
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeFactorization
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence
public import StacksFrontier.AlgebraicGeometry.ProjMapTwistDegreeSection.Basic
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree

/-!
# Full scheme-theoretic trisecants and quadratic equations

A quadratic on the actual projective line vanishing on a closed scheme
of structural H0 at least three is zero. Surjectivity of the original
finite affine restriction proves this for double and triple points too.
Consequently a genuine projective line whose intersection with an
actual quadratically defined subscheme contains such a closed scheme
factors through that subscheme, as a SCHEME morphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.ProjectiveSpace.Cohomology
open Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection
open M9Native.ProjectiveQuadraticCohomology M9Native.ProjectiveQuadraticDimension

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace M9Native.QuadraticTrisecant

variable (K : Type u) [Field K]

theorem projectiveLine_dimension_le_one : topologicalKrullDim (projective K 1) ≤ 1 := by
  have h := Stacks.ProjectiveSpace.topologicalKrullDim_proj_fin K (r := 2) (by decide)
  simpa only [Nat.reduceSub, Nat.cast_one] using h.le

/-- Length is that of the FULL original closed scheme. No reducedness,
distinct-point decomposition, or finiteness assumption on D is used. -/
theorem quadratic_eval_eq_zero_of_ideal_le
    (D : (projective K 1).IdealSheafData)
    (hD : 3 ≤ Module.finrank K
      (structureSheafCohomology (D.subschemeι ≫ projToSpecCoeff K 1) 0))
    (s : (twist K 1 2).sections) (hvan : quadraticIdeal K 1 s ≤ D) :
    s.eval (op ⊤) = 0 := by
  by_contra hs
  letI : IsProper (projToSpecCoeff K 1) :=
    Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff K 1
  letI : IsFinite (quadraticProjection K 1 s) :=
    isFinite_zeroScheme_of_eval_top_ne_zero K (projToSpecCoeff K 1)
      (projectiveLine_dimension_le_one K) (twist K 1 2) s hs
  have hlen := FiniteClosedSectionH0.h0_le_of_ideal_le K (projToSpecCoeff K 1)
    (quadraticIdeal K 1 s) D hvan
  have hquad := finite_quadratic_h0_le_two K 1 s
  change Module.finrank K (structureSheafCohomology
    ((quadraticIdeal K 1 s).subschemeι ≫ projToSpecCoeff K 1) 0) ≤ 2 at hquad
  omega

/-- Actual vanishing of the pulled section is enough: ideal
containment is DERIVED by the native universal zero-scheme property. -/
theorem quadratic_eval_eq_zero_of_pullback_eq_zero
    (D : (projective K 1).IdealSheafData)
    (hD : 3 ≤ Module.finrank K
      (structureSheafCohomology (D.subschemeι ≫ projToSpecCoeff K 1) 0))
    (s : (twist K 1 2).sections)
    (hvan : pullbackGlobalSections D.subschemeι (twist K 1 2) (s.eval (op ⊤)) = 0) :
    s.eval (op ⊤) = 0 := by
  apply quadratic_eval_eq_zero_of_ideal_le K D hD s
  exact (zeroScheme_isGreatest_vanishingClosedSubscheme (projective K 1)
    (twist K 1 2) (s.eval (op ⊤))).2 hvan

/-- For a genuine homogeneous quadratic the original polynomial is zero. -/
theorem quadratic_polynomial_eq_zero_of_ideal_le
    (D : (projective K 1).IdealSheafData)
    (hD : 3 ≤ Module.finrank K
      (structureSheafCohomology (D.subschemeι ≫ projToSpecCoeff K 1) 0))
    (F : polyGrading K 1 2)
    (hvan : quadraticIdeal K 1 (polynomialSection K 1 F) ≤ D) :
    (F : MvPolynomial (Fin 2) K) = 0 := by
  have hs := quadratic_eval_eq_zero_of_ideal_le K D hD (polynomialSection K 1 F) hvan
  rw [polynomialSection_eval] at hs
  by_contra hF
  exact degreeSection_ne_zero K 1 2 F hF hs

section ActualLinearLine

variable (n : ℕ) (ψ : polyGrading K n →+*ᵍ polyGrading K 1)
    (hψ : Function.Surjective ψ)

/-- The actual projective LINE immersion, from the original graded quotient. -/
def linearMap : projective K 1 ⟶ projective K n :=
  Proj.map ψ (Proj.irrelevant_le_map_of_surjective ψ hψ)

instance linearMap_closed : IsClosedImmersion (linearMap K n ψ hψ) :=
  Proj.isClosedImmersion_map_of_surjective' ψ hψ

def restrictedForm (F : polyGrading K n 2) : polyGrading K 1 2 :=
  ⟨ψ F, ψ.map_mem F.property⟩

private theorem pullbackGlobal_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (s : Γ(M, ⊤)) : pullbackGlobalSections f M s =
      Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection f M s := by
  change ((Scheme.Modules.pullback f).obj M).presheaf.map
      (eqToHom (show f ⁻¹ᵁ (⊤ : Y.Opens) = ⊤ from rfl)).op
      (Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection f M s) = _
  exact Functor.map_id_apply _ _ _

/-- Exact pulled-back quadratic ideal, not an equality of zero sets. -/
theorem quadraticIdeal_comap_linearMap (F : polyGrading K n 2) :
    (quadraticIdeal K n (polynomialSection K n F)).comap (linearMap K n ψ hψ) =
      quadraticIdeal K 1 (polynomialSection K 1 (restrictedForm K n ψ F)) := by
  rw [quadraticIdeal, ← Stacks.Divisors.zeroScheme_pullback]
  dsimp only [quadraticIdeal]
  rw [polynomialSection_eval, polynomialSection_eval]
  apply zeroScheme_eq_of_iso
    (pullbackTwistIso ψ (Proj.irrelevant_le_map_of_surjective ψ hψ) hψ
      (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n+1)) K) 2)
  rw [pullbackGlobal_eq]
  exact pullbackTwistIso_degreeSection ψ (Proj.irrelevant_le_map_of_surjective ψ hψ) hψ
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n+1)) K) 2 F

/-- Every actual quadratic equation vanishing on the full length-three
subscheme restricts to the ZERO polynomial on the actual line. -/
theorem restrictedForm_eq_zero_of_trisecant
    (D : (projective K 1).IdealSheafData)
    (hD : 3 ≤ Module.finrank K
      (structureSheafCohomology (D.subschemeι ≫ projToSpecCoeff K 1) 0))
    (F : polyGrading K n 2)
    (hvan : (quadraticIdeal K n (polynomialSection K n F)).comap
      (linearMap K n ψ hψ) ≤ D) :
    (restrictedForm K n ψ F : MvPolynomial (Fin 2) K) = 0 := by
  rw [quadraticIdeal_comap_linearMap K n ψ hψ F] at hvan
  exact quadratic_polynomial_eq_zero_of_ideal_le K D hD _ hvan

/-- Actual ideal generation by quadrics, not merely set-theoretic
generation, forces the whole line into the original closed subscheme. -/
theorem quadratic_generated_comap_eq_bot
    {ι : Type u} (F : ι → polyGrading K n 2)
    (I : (projective K n).IdealSheafData)
    (hI : I = ⨆ a, quadraticIdeal K n (polynomialSection K n (F a)))
    (D : (projective K 1).IdealSheafData)
    (hD : 3 ≤ Module.finrank K
      (structureSheafCohomology (D.subschemeι ≫ projToSpecCoeff K 1) 0))
    (hvan : I.comap (linearMap K n ψ hψ) ≤ D) :
    I.comap (linearMap K n ψ hψ) = ⊥ := by
  apply le_antisymm _ bot_le
  apply (Scheme.IdealSheafData.le_map_iff_comap_le).mp
  rw [hI]
  apply iSup_le
  intro a
  apply (Scheme.IdealSheafData.le_map_iff_comap_le).mpr
  have hQa : quadraticIdeal K n (polynomialSection K n (F a)) ≤ I := by
    rw [hI]
    exact le_iSup (fun a => quadraticIdeal K n (polynomialSection K n (F a))) a
  have hz := restrictedForm_eq_zero_of_trisecant K n ψ hψ D hD (F a)
    ((Scheme.IdealSheafData.comap_mono (linearMap K n ψ hψ) hQa).trans hvan)
  rw [quadraticIdeal_comap_linearMap K n ψ hψ]
  have hpoly : restrictedForm K n ψ (F a) = 0 := Subtype.ext hz
  rw [hpoly]
  dsimp only [quadraticIdeal]
  rw [polynomialSection_eval]
  have hsec : degreeSection (polyGrading K 1) 2 0 = 0 := by
    unfold degreeSection
    exact map_zero _
  rw [hsec, zeroScheme_zero]

/-- The result is a factorization of actual SCHEME morphisms. -/
theorem factorsThrough_of_quadratic_trisecant
    {ι : Type u} (F : ι → polyGrading K n 2)
    (I : (projective K n).IdealSheafData)
    (hI : I = ⨆ a, quadraticIdeal K n (polynomialSection K n (F a)))
    (D : (projective K 1).IdealSheafData)
    (hD : 3 ≤ Module.finrank K
      (structureSheafCohomology (D.subschemeι ≫ projToSpecCoeff K 1) 0))
    (hvan : I.comap (linearMap K n ψ hψ) ≤ D) :
    ∃ g : projective K 1 ⟶ I.subscheme,
      g ≫ I.subschemeι = linearMap K n ψ hψ := by
  apply (factorsThrough_ideal_iff_ideal_le_ker I (linearMap K n ψ hψ)).mpr
  have h : I ≤ (⊥ : (projective K 1).IdealSheafData).map (linearMap K n ψ hψ) := by
    apply (Scheme.IdealSheafData.le_map_iff_comap_le).mpr
    rw [quadratic_generated_comap_eq_bot K n ψ hψ F I hI D hD hvan]
  simpa only [Scheme.IdealSheafData.map_bot] using h

end ActualLinearLine
end M9Native.QuadraticTrisecant
