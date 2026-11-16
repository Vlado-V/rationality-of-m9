module

public import M9StacksIntegration.CurveDivisorDegree
public import M9StacksIntegration.DualizingDivisorRestriction
public import M9StacksIntegration.CanonicalLineCohomology
public import M9StacksIntegration.SmoothCurveCanonicalDifferentials

/-!
# Geometric Riemann--Roch for the actual canonical divisor restriction

The rank of the ORIGINAL canonical restriction plus h0(O(D)) is
length(D)+1. Native Serre duality, the actual ideal restriction row,
and the native line-degree formula prove it, with no no-pencil or
canonical-embedding premise. Nonreduced effective divisors are retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Duality
open M9Native.CurveDivisorSections

universe u

namespace M9Native.CanonicalDivisorSpan

variable {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsProper f] [IsCurve K f] [Smooth f]
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)]

local instance canonicalInvertible :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property (dualizingSheafOverField f) :=
  CurveCanonicalInvertibility.dualizing_isInvertible f

/-- The original native H0 restriction, before any projective-span identification. -/
abbrev canonicalRestriction (D : X.IdealSheafData) :=
  (cohomologyOverFieldMap K f (restrictionπ D (dualizingSheafOverField f)) 0).hom

/-- Full geometric Riemann--Roch on the actual finite Cartier scheme. -/
theorem restriction_rank_add_divisor_h0 (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    letI : Algebra K Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
    Module.finrank K (LinearMap.range (canonicalRestriction f D)) +
      Module.finrank K (cohomologyOverField K f (Stacks.Divisors.invertibleSheaf' D) 0) =
        Module.finrank K Γ(D.subscheme, ⊤) + 1 := by
  letI : Algebra K Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
  letI := modulesLinearOverField K f
  let hdim : topologicalKrullDim X ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := K) (f := f)).le
  let W := dualizingSheafOverField f
  let T := twistDown D W
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property W :=
    canonicalInvertible f
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property T :=
    CurveDivisorSections.twistDown_isInvertible D W
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : T.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X T
  letI : Module.Finite K (cohomologyOverField K f T 1) :=
    finiteDimensional_cohomologyOverField_of_isProper K f T 1
  have hdual : Module.finrank K (T ⟶ W) =
      Module.finrank K (cohomologyOverField K f T 1) :=
    (homDualizingSheafLinearEquiv f hdim T (isQuasicoherent_of_isCoherent T)).finrank_eq.trans
      Subspace.dual_finrank_eq
  have hhom := M9StacksIntegration.DualizingDivisorRestriction.finrank_hom_twistDown f W D
  have h1 : Module.finrank K (cohomologyOverField K f T 1) =
      Module.finrank K (cohomologyOverField K f (Stacks.Divisors.invertibleSheaf' D) 0) :=
    hdual.symm.trans hhom
  have hdegree : invertibleCurveDegree K f hdim T =
      2 * (genus f : ℤ) - 2 - (Module.finrank K Γ(D.subscheme, ⊤) : ℤ) := by
    change invertibleCurveDegree K f hdim (twistDown D (dualizingSheafOverField f)) = _
    rw [CurveDivisorDegree.twistDown_degree f hdim D,
      CanonicalLineCohomology.canonical_degree f hdim]
  have hRR := finrank_sub_finrank_eq_invertibleCurveDegree_add_genus K f hdim T
  rw [h1, hdegree] at hRR
  have hr := restriction_range_finrank_add_twistDown f D W
  have hW := finrank_cohomologyOverField_zero_dualizingSheafOverField f hdim
  change Module.finrank K (LinearMap.range (canonicalRestriction f D)) +
    Module.finrank K (cohomologyOverField K f T 0) =
      Module.finrank K (cohomologyOverField K f (dualizingSheafOverField f) 0) at hr
  rw [hW] at hr
  omega

/-- A divisor moving in a pencil has canonical linear-span dimension
at most length(D)-2, expressed first as the actual evaluation rank. -/
theorem restriction_rank_le_length_sub_one (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hmove : 2 ≤ Module.finrank K
      (cohomologyOverField K f (Stacks.Divisors.invertibleSheaf' D) 0)) :
    letI : Algebra K Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
    Module.finrank K (LinearMap.range (canonicalRestriction f D)) ≤
      Module.finrank K Γ(D.subscheme, ⊤) - 1 := by
  letI : Algebra K Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
  have h := restriction_rank_add_divisor_h0 f D
  omega

end M9Native.CanonicalDivisorSpan
