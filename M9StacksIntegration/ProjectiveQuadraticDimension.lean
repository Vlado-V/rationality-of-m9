module

public import M9StacksIntegration.ProjectiveQuadraticCohomology
public import M9StacksIntegration.IntegralLineCutSerreDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.DimensionOfProjectiveSpace
public import Mathlib.AlgebraicGeometry.Artinian
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Smooth

/-!
# Finiteness forces a quadratic section's ambient space to be a point or line

The dimension restriction is derived from actual finiteness. A nonzero
quadratic in P^n for n>=2 is nonempty by its actual H0 sequence, and the
Cartier dimension theorem gives dimension n-1. The zero polynomial gives
all of P^n. Neither can be finite when n>=2.

The short affine finite-to-Artinian argument below is the geometric
argument of pinned StacksFrontier EtaleCohomology/Trace/DimensionZeroWeights
lines 56-80 (Apache 2.0), stated here without importing its etale machinery.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.ProjectiveSpace.Cohomology
open M9Native.ProjectiveQuadraticCohomology
universe u
attribute [local instance] MvPolynomial.gradedAlgebra HasDerivedCategory.standard

namespace M9Native.ProjectiveQuadraticDimension
variable (K : Type u) [Field K]

/-- Actual finite schemes over the original field, including the empty scheme. -/
theorem dimension_le_zero_of_finite {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsFinite f] :
    topologicalKrullDim X ≤ 0 := by
  let : IsAffine X := isAffine_of_isAffineHom f
  let φ : K →+* Γ(X, ⊤) := f.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  have hφ : φ.Finite := RingHom.Finite.comp (f.finite_app ⊤ (isAffineOpen_top _))
    (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm.surjective)
  let := φ.toAlgebra
  let : Module.Finite K Γ(X, ⊤) := hφ
  let : IsArtinianRing Γ(X, ⊤) := IsArtinianRing.of_finite K Γ(X, ⊤)
  let e : X ≃ₜ PrimeSpectrum Γ(X, ⊤) := Scheme.homeoOfIso X.isoSpec
  let : DiscreteTopology X := e.isEmbedding.discreteTopology
  exact topologicalKrullDim_zero_of_discreteTopology X

abbrev polynomialSection (n : ℕ) (F : polyGrading K n 2) : (twist K n 2).sections :=
  Stacks.PresheafOfModules.sectionOfTop (twist K n 2).val (degreeSection (polyGrading K n) 2 F)

theorem polynomialSection_eval (n : ℕ) (F : polyGrading K n 2) :
    (polynomialSection K n F).eval (op ⊤) = degreeSection (polyGrading K n) 2 F :=
  Stacks.PresheafOfModules.sectionOfTop_val_top (twist K n 2).val _

theorem nonempty_of_two_le (n : ℕ) (hn : 2 ≤ n) (F : polyGrading K n 2)
    (hF : (F : MvPolynomial (Fin (n+1)) K) ≠ 0) :
    Nonempty (quadraticIdeal K n (polynomialSection K n F)).subscheme := by
  let I := quadraticIdeal K n (polynomialSection K n F)
  have hker : I.subschemeι.ker = zeroScheme (projective K n) (twist K n 2)
      (degreeSection (polyGrading K n) 2 F) := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    dsimp only [I, quadraticIdeal]
    rw [polynomialSection_eval]
  obtain ⟨e⟩ := nonempty_structureSheafCohomologyIsoTwistCohomologyZero K n 0 2
    I.subschemeι F hF hker
    (isZero_twistCohomology K n (-2) 0 (by omega))
    (isZero_twistCohomology K n (-2) 1 (by omega))
  have hH0 : Module.finrank K (structureSheafCohomology
      (I.subschemeι ≫ projToSpecCoeff K n) 0) = 1 :=
    (e ≪≫ twistCohomologyZeroIsoCoeff K n).toLinearEquiv.finrank_eq.trans (Module.finrank_self K)
  by_contra h
  let : IsEmpty I.subscheme := not_nonempty_iff.mp h
  let : Subsingleton Γ(SheafOfModules.unit I.subscheme.ringCatSheaf, ⊤) := by
    change Subsingleton Γ(I.subscheme, ⊤)
    infer_instance
  let : Subsingleton (cohomologyOverField K (I.subschemeι ≫ projToSpecCoeff K n)
      (SheafOfModules.unit I.subscheme.ringCatSheaf) 0) :=
    (cohomologyOverFieldZeroEquivSections K (I.subschemeι ≫ projToSpecCoeff K n)
      (SheafOfModules.unit I.subscheme.ringCatSheaf)).subsingleton
  let : Subsingleton (structureSheafCohomology (I.subschemeι ≫ projToSpecCoeff K n) 0) :=
    (structureSheafCohomologyIsoCohomologyOverField K
      (I.subschemeι ≫ projToSpecCoeff K n) 0).toLinearEquiv.toEquiv.subsingleton
  have hh : Module.finrank K (structureSheafCohomology
      (I.subschemeι ≫ projToSpecCoeff K n) 0) = 0 := Module.finrank_zero_of_subsingleton
  exact one_ne_zero (hH0.symm.trans hh)

/-- No ambient point/line restriction is supplied: it follows from true finiteness. -/
theorem ambient_le_one_of_finite (n : ℕ) (F : polyGrading K n 2)
    [IsFinite (quadraticProjection K n (polynomialSection K n F))] : n ≤ 1 := by
  by_contra hn
  have hn2 : 2 ≤ n := by omega
  let I := quadraticIdeal K n (polynomialSection K n F)
  let p := projToSpecCoeff K n
  let : Smooth p := Stacks.AlgebraicGeometry.ProjPolyChart.smooth_projToSpecCoeff K n
  have hdim : topologicalKrullDim (projective K n) = (n : WithBot ℕ∞) := by
    simpa only [Nat.add_sub_cancel] using Stacks.ProjectiveSpace.topologicalKrullDim_proj_fin K
      (r := n+1) n.succ_pos
  have hfin : topologicalKrullDim I.subscheme ≤ 0 :=
    dimension_le_zero_of_finite K (quadraticProjection K n (polynomialSection K n F))
  by_cases hF : (F : MvPolynomial (Fin (n+1)) K) = 0
  · have hs : degreeSection (polyGrading K n) 2 F = 0 := by
      have he : F = 0 := Subtype.ext hF
      subst F
      unfold degreeSection
      exact map_zero _
    have hI : I = ⊥ := by
      dsimp only [I, quadraticIdeal]
      rw [polynomialSection_eval, hs, zeroScheme_zero]
    let : IsIso I.subschemeι := (Scheme.isIso_subschemeι_iff_eq_bot I).mpr hI
    have he := I.subschemeι.homeomorph.isHomeomorph.topologicalKrullDim_eq I.subschemeι
    have hc : (n : WithBot ℕ∞) ≤ 0 := hdim ▸ he ▸ hfin
    have : n ≤ 0 := by exact_mod_cast hc
    omega
  · have hne := nonempty_of_two_le K n hn2 F hF
    have hs : (polynomialSection K n F).eval (op ⊤) ≠ 0 := by
      rw [polynomialSection_eval]
      exact degreeSection_ne_zero K n 2 F hF
    have hd := IntegralLineCutSerreDimension.zeroScheme_components_dimension K p (twist K n 2)
      ((polynomialSection K n F).eval (op ⊤)) hs n hdim hne
    have hc : ((n-1 : ℕ) : WithBot ℕ∞) ≤ 0 := hd.2 ▸ hfin
    have : n-1 ≤ 0 := by exact_mod_cast hc
    omega

end M9Native.ProjectiveQuadraticDimension
