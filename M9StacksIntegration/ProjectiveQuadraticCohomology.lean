module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.HypersurfaceCohomology
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.GlobalFunctions
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField

/-!
# Scheme length of a finite projective quadratic zero scheme

The actual zero-scheme sequence is used, including nonreduced zero schemes.
The cohomology bound is derived from the original coefficient-linear long
exact sequence and Serre's actual computation of O(-2), with no length or
ambient-dimension bound supplied.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.ProjectiveSpace.Cohomology
universe u

attribute [local instance] MvPolynomial.gradedAlgebra HasDerivedCategory.standard

namespace M9Native.ProjectiveQuadraticCohomology
variable (K : Type u) [Field K]

abbrev projective (n : ℕ) := AlgebraicGeometry.Proj (polyGrading K n)
abbrev twist (n : ℕ) (d : ℤ) := twistingSheafModule (polyGrading K n) d

local instance modulesMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.sheafTensorMonoidal X.sheaf.obj X.ringCatSheaf.property

/-- The original structural K-action, rather than an abstract scalar identification. -/
def unitH0IsoCoeff (n : ℕ) :
    cohomologyOverField K (projToSpecCoeff K n)
      (SheafOfModules.unit (projective K n).ringCatSheaf) 0 ≅ ModuleCat.of K K :=
  (cohomologyOverFieldIso K (projToSpecCoeff K n)
      (Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit (polyGrading K n)) 0).symm ≪≫
    cohomologyOverFieldIsoRestrictScalarsCoeffScalar K n _ 0 ≪≫ twistCohomologyZeroIsoCoeff K n

/-- Serre's ready polynomial formula at (-2) is dual to degree-zero polynomials. -/
theorem line_minus_two_h1 :
    Module.finrank K (twistCohomology K 1 (-2) 1) = 1 := by
  let e0 := (serreTwistCohomology K 0 0).degreeZeroPolynomial (by decide)
  let e1 := (serreTwistCohomology K 0 (-2)).degreeTopPolynomial (by decide)
  let : Module.Finite K (twistCohomology K 1 0 0) := moduleFinite_twistCohomology K 1 0 0
  let : Module.Finite K (MvPolynomial.homogeneousSubmodule (Fin 2) K 0) :=
    Module.Finite.equiv e0.toLinearEquiv
  calc
    Module.finrank K (twistCohomology K 1 (-2) 1) =
        Module.finrank K (MvPolynomial.homogeneousSubmodule (Fin 2) K 0 →ₗ[K] K) :=
      e1.toLinearEquiv.finrank_eq
    _ = Module.finrank K (MvPolynomial.homogeneousSubmodule (Fin 2) K 0) := by
      rw [Module.finrank_linearMap, Module.finrank_self, mul_one]
    _ = Module.finrank K (twistCohomology K 1 0 0) := e0.toLinearEquiv.finrank_eq.symm
    _ = 1 := (twistCohomologyZeroIsoCoeff K 1).toLinearEquiv.finrank_eq.trans (Module.finrank_self K)

theorem twist_minus_two_h1_le_one (n : ℕ) :
    Module.finrank K (cohomologyOverField K (projToSpecCoeff K n) (twist K n (-2)) 1) ≤ 1 := by
  rw [(cohomologyOverFieldIsoRestrictScalarsCoeffScalar K n _ 1).toLinearEquiv.finrank_eq]
  change Module.finrank K (twistCohomology K n (-2) 1) ≤ 1
  by_cases hn : n = 1
  · subst n
    exact (line_minus_two_h1 K).le
  · let := ModuleCat.subsingleton_of_isZero (isZero_twistCohomology K n (-2) 1 (by omega))
    rw [Module.finrank_zero_of_subsingleton]
    omega

abbrev quadraticIdeal (n : ℕ) (s : (twist K n 2).sections) :=
  zeroScheme (projective K n) (twist K n 2) (s.eval (op ⊤))
abbrev quadraticProjection (n : ℕ) (s : (twist K n 2).sections) :=
  (quadraticIdeal K n s).subschemeι ≫ projToSpecCoeff K n

/-- Actual finite projective quadratic zero schemes have H0-dimension at most two.
No reducedness, ambient-dimension bound, or nonzero-section premise is supplied. -/
theorem finite_quadratic_h0_le_two (n : ℕ) (s : (twist K n 2).sections)
    [IsFinite (quadraticProjection K n s)] :
    Module.finrank K (structureSheafCohomology (quadraticProjection K n s) 0) ≤ 2 := by
  let X := projective K n
  let L := twist K n 2
  let I := quadraticIdeal K n s
  let p := projToSpecCoeff K n
  let Q := (Scheme.Modules.pushforward I.subschemeι).obj
    (SheafOfModules.unit I.subscheme.ringCatSheaf)
  have he : Module.finrank K (structureSheafCohomology (quadraticProjection K n s) 0) =
      Module.finrank K (cohomologyOverField K p Q 0) :=
    (structureSheafCohomologyIsoCohomologyOverFieldSubscheme K p I.subschemeι I
      (Scheme.IdealSheafData.ker_subschemeι I) 0).toLinearEquiv.finrank_eq
  rw [he]
  by_cases hs : s.eval (op ⊤) = 0
  · have hI : I = ⊥ := by
      dsimp only [I, quadraticIdeal]
      rw [hs, zeroScheme_zero]
    let : IsIso I.subschemeι := (Scheme.isIso_subschemeι_iff_eq_bot I).mpr hI
    let e := Stacks.Morphisms.pushforwardStructureSheafIsoUnit (asIso I.subschemeι)
    have h := (cohomologyOverFieldIso K p e 0 ≪≫ unitH0IsoCoeff K n).toLinearEquiv.finrank_eq
    exact h.trans_le (by simp)
  · let : IsFinite (I.subschemeι ≫ p) := (inferInstance : IsFinite (quadraticProjection K n s))
    let : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian (I.subschemeι ≫ p)
    let : (SheafOfModules.unit I.subscheme.ringCatSheaf).IsCoherent := inferInstance
    let : Module.Finite K (cohomologyOverField K p Q 0) :=
      finiteDimensional_cohomologyOverField_pushforward_of_isFinite K I.subschemeι p _ 0
    let : Module.Finite K (cohomologyOverField K p (SheafOfModules.unit X.ringCatSheaf) 0) :=
      Module.Finite.equiv (unitH0IsoCoeff K n).symm.toLinearEquiv
    let : Module.Finite K (twistCohomology K n (-2) 1) :=
      moduleFinite_twistCohomology K n (-2) 1
    let : Module.Finite K (cohomologyOverField K p (twist K n (-2)) 1) :=
      Module.Finite.equiv (cohomologyOverFieldIsoRestrictScalarsCoeffScalar K n _ 1).symm.toLinearEquiv
    obtain ⟨a,b,w,hS⟩ := exists_shortExact_zeroScheme_unit_of_isRegularSection
      X L s (isRegularSection_of_eval_top_ne_zero L s hs) (twist K n (-2))
      (twistNegTensorIsoUnit (polyGrading K n)
        (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n+1)) K) 2)
    obtain ⟨d,-,-,hBC,-⟩ := exists_cohomologyOverField_longExactSequence K p hS
    let a0 : cohomologyOverField K p (SheafOfModules.unit X.ringCatSheaf) 0 →ₗ[K]
        cohomologyOverField K p Q 0 := (cohomologyOverFieldMap K p b 0).hom
    let d0 : cohomologyOverField K p Q 0 →ₗ[K]
        cohomologyOverField K p (twist K n (-2)) 1 := (d 0).hom
    have hex : Function.Exact a0 d0 := hBC 0
    have hr := d0.finrank_range_add_finrank_ker
    rw [hex.linearMap_ker_eq] at hr
    have ha := LinearMap.finrank_range_le a0
    have hd := Submodule.finrank_le (LinearMap.range d0)
    have hu : Module.finrank K
        (cohomologyOverField K p (SheafOfModules.unit X.ringCatSheaf) 0) = 1 :=
      (unitH0IsoCoeff K n).toLinearEquiv.finrank_eq.trans (Module.finrank_self K)
    have ht : Module.finrank K (cohomologyOverField K p (twist K n (-2)) 1) ≤ 1 :=
      twist_minus_two_h1_le_one K n
    change Module.finrank K (cohomologyOverField K p Q 0) ≤ 2
    omega

end M9Native.ProjectiveQuadraticCohomology
