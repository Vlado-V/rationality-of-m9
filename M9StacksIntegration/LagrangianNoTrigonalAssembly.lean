module
public import M9StacksIntegration.LagrangianTransverseMixedIdeal
public import M9StacksIntegration.LagrangianTransversePositiveGenus
public import M9StacksIntegration.CanonicalQuadricsNoTrigonal

/-! Exact assembly on the ORIGINAL transverse five-row curve.
All canonical, scalar, row-cut and positive-genus inputs are theorems.
The remaining explicit input is the actual LG polynomial image ideal;
the unconditional application must supply its geometric proof. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)
open Stacks.AlgebraicGeometry.ProjBaseChange (polynomialComparison)
open M9Native.ProjectiveQuadraticCohomology M9Native.ProjectiveQuadraticDimension
universe u

namespace M9Native.LagrangianNoTrigonalAssembly
open LagrangianTransverseRestriction LagrangianTransverseProjectiveCanonical
open LagrangianPolynomialPluckerFrame LagrangianPolynomialLinearRows LagrangianTransverseMixedIdeal

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    (M : Matrix (Fin 5) (Fin 14) K)
    [IsIntegral (curve K M)] [SmoothOfRelativeDimension 1 (curveProjection K M)]

theorem curveDimension_le_one : topologicalKrullDim (curve K M) ≤ 1 :=
  (IsCurve.topologicalKrullDim_eq_one (k := K) (f := curveProjection K M)).le

/-- The only explicit geometric gate is the ORIGINAL LG image ideal,
not any pencil/span/section comparison conclusion. -/
theorem no_g1_three_of_polynomial_kernel_eq_quadrics (hM : Function.Surjective M.mulVec)
    {ι : Type u} (Q : ι → polyGrading K 13 2)
    (hLG : (polynomialPlucker K).ker =
      ⨆ j, quadraticIdeal K 13 (polynomialSection K 13 (Q j))) :
    ¬ Nonempty (LinearSeries K (curveProjection K M) (curveDimension_le_one K M) 3 1) := by
  let f := curveProjection K M
  letI : IsProper f := curve_proper K M
  letI : IsCurve K f := curve_isCurve K M
  letI : Smooth f := SmoothOfRelativeDimension.smooth 1 _
  letI : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop) :=
    isIso_globalSections_of_isAlgClosed K f
  let κ := projectiveMap K M
  letI : IsClosedImmersion κ := projectiveMap_isClosedImmersion K M
  have hI : (κ ≫ (polynomialComparison K 13).iso.hom).ker =
      (⨆ j : Fin 5, MixedQuadraticTrisecant.degreeIdeal K 13 1 (rowPolynomial K M j)) ⊔
        (⨆ j, quadraticIdeal K 13 (polynomialSection K 13 (Q j))) := by
    have hmap : κ ≫ (polynomialComparison K 13).iso.hom =
        inclusion K M ≫ polynomialPlucker K :=
      Category.assoc (inclusion K M) (LagrangianPlucker.primitivePlucker K)
        (polynomialComparison K 13).iso.hom
    rw [hmap]
    change (inclusion K M ≫ polynomialPlucker K).ker = rowAmbientIdeal K M ⊔ _
    exact (polynomial_inclusion_kernel K M).trans
      (congrArg (fun J => rowAmbientIdeal K M ⊔ J) hLG)
  have hI' : (κ ≫ (polynomialComparison K 13).iso.hom).ker =
      (⨆ j : ULift.{u} (Fin 5),
        MixedQuadraticTrisecant.degreeIdeal K 13 1 (rowPolynomial K M j.down)) ⊔
        (⨆ j, quadraticIdeal K 13 (polynomialSection K 13 (Q j))) := by
    simpa only [iSup_ulift] using hI
  exact CanonicalQuadricsNoTrigonal.no_g1_three (K := K) (X := curve K M)
    (ι := ULift.{u} (Fin 5)) (κq := ι) f (curveDimension_le_one K M) 13 (by decide)
    κ (projectiveMap_overBase K M) (canonicalO1Iso K M hM)
    (LagrangianTransversePositiveGenus.genus_ne_zero K M hM)
    (fun j => rowPolynomial K M j.down) Q hI'

end M9Native.LagrangianNoTrigonalAssembly
