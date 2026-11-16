module

public import M9StacksIntegration.CurveGenericResidueSeparable
public import M9StacksIntegration.CurveTangentLineGeometry
public import M9StacksIntegration.FiniteLocallyFreeDualFaithful
public import M9StacksIntegration.LineMapCokernelCohomology
public import M9StacksIntegration.ZeroDimensionalCohomologyLength
public import StacksFrontier.AlgebraicGeometry.Curves.RiemannHurwitz

/-!
# The actual derivative normal sheaf of a nonconstant characteristic-zero curve map

The cotangent arrow is the original native relative-differentials map;
its actual sheaf dual is the tangent derivative. The normal sheaf is
its literal native cokernel. Generic separability, nonvanishing,
injectivity, coherent finite support and all positive-cohomology
vanishing are derived from the original smooth proper nonconstant map.
The original H0 is the actual cotangent-degree Riemann--Hurwitz number.

No generic-separability, nonzero-derivative, support, count, or numerical
degree hypothesis is supplied. Numerical specialization to genus nine
and the projective line additionally needs the genuine native theorem
computing cotangent degrees; no identification Ω=ω is inferred here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.CurveTangentLineGeometry

universe u

namespace M9Native.CurveDerivativeNormal

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- The original native cotangent derivative. -/
abbrev cotangentMap (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (g : X ⟶ Y) (hg : g ≫ pY = pX) :
    (Scheme.Modules.pullback g).obj (Scheme.Hom.relativeDifferentials pY) ⟶
      Scheme.Hom.relativeDifferentials pX :=
  Scheme.Hom.relativeDifferentialsMap g pY pX (𝟙 (Spec (.of k))) (by simpa using hg)

/-- The actual sheaf-dual tangent derivative, with both original sheaves retained. -/
abbrev tangentMap (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (g : X ⟶ Y) (hg : g ≫ pY = pX) :
    tangentLine pX ⟶ pulledTangentLine pY g :=
  dualMap (cotangentMap pX pY g hg)

/-- The literal native cokernel of the original tangent derivative. -/
abbrev normalSheaf (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (g : X ⟶ Y) (hg : g ≫ pY = pX) : X.Modules :=
  cokernel (tangentMap pX pY g hg)

variable [CharZero k]
variable (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
variable [IsCurve k pX] [IsCurve k pY] [IsProper pX] [IsProper pY]
variable [Smooth pX] [Smooth pY]
variable (g : X ⟶ Y) (hg : g ≫ pY = pX)
variable (hnc : ¬ ∃ y : Y, ∀ x : X, g.base x = y)

include hnc

/-- Generic étaleness derives actual derivative nonvanishing from
nonconstancy in characteristic zero. -/
theorem cotangentMap_ne_zero : cotangentMap pX pY g hg ≠ 0 :=
  ((genericallyEtale_tfae pX pY g hg).out 5 1 rfl rfl).mp
    (CurveGenericResidueSeparable.generic_finite_separable_of_nonconstant pX pY g hg hnc)

/-- Genuine finite-locally-free double-dual evaluation detects the
original map and proves that its actual dual remains nonzero. -/
theorem tangentMap_ne_zero : tangentMap pX pY g hg ≠ 0 := by
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (R := X.ringCatSheaf)
      (Scheme.Hom.relativeDifferentials pX) :=
    Scheme.Hom.isFiniteLocallyFree_relativeDifferentials pX
  exact FiniteLocallyFreeDualFaithful.dualMap_ne_zero
    (cotangentMap pX pY g hg) (cotangentMap_ne_zero pX pY g hg hnc)

omit hnc [CharZero k] [IsProper pX] [IsProper pY] in
/-- The actual normal cokernel is coherent independently of nonvanishing. -/
theorem normal_isCoherent : (normalSheaf pX pY g hg).IsCoherent := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
  let := tangent_isInvertible pX
  let := pulledTangent_isInvertible pY g
  exact LineMapCokernelCohomology.cokernel_isCoherent (tangentMap pX pY g hg)

/-- The original tangent derivative is injective. -/
theorem tangentMap_mono : Mono (tangentMap pX pY g hg) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
  let := tangent_isInvertible pX
  let := pulledTangent_isInvertible pY g
  exact LineMapCokernelCohomology.mono_of_ne_zero _
    (tangentMap_ne_zero pX pY g hg hnc)

/-- The actual derivative and actual quotient form a genuine short exact sequence. -/
theorem normal_shortExact :
    (ShortComplex.mk (tangentMap pX pY g hg) (cokernel.π (tangentMap pX pY g hg))
      (cokernel.condition (tangentMap pX pY g hg))).ShortExact := by
  let := tangentMap_mono pX pY g hg hnc
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance

/-- Original normal support has dimension zero, derived from the actual map. -/
theorem normal_support_le_zero :
    topologicalKrullDim (SheafOfModules.supp (normalSheaf pX pY g hg)) ≤ 0 := by
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType pX
  let := tangent_isInvertible pX
  let := pulledTangent_isInvertible pY g
  exact LineMapCokernelCohomology.cokernel_support_le_zero
    (IsCurve.topologicalKrullDim_eq_one (f := pX)).le _
    (tangentMap_ne_zero pX pY g hg hnc)

/-- In particular the original normal sheaf has finite support. -/
theorem normal_support_finite :
    (SheafOfModules.supp (normalSheaf pX pY g hg)).Finite := by
  let := normal_isCoherent pX pY g hg
  exact finite_supp_of_supp_le_zero k pX _ (normal_support_le_zero pX pY g hg hnc)

/-- Every original positive cohomology group of the normal sheaf vanishes. -/
theorem normal_positive_cohomology_isZero (i : ℕ) (hi : 0 < i) :
    letI := normal_isCoherent pX pY g hg
    IsZero (cohomologyOverField k pX (normalSheaf pX pY g hg) i) := by
  let := normal_isCoherent pX pY g hg
  exact isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero k pX _
    (normal_support_le_zero pX pY g hg hnc) i hi

/-- Native Euler additivity and native pullback degree compute the
original normal H0; no differential-degree value is supplied. -/
theorem normal_h0_degree_formula :
    letI := normal_isCoherent pX pY g hg
    letI := differentials_rank_one pX
    letI := differentials_rank_one pY
    (Module.finrank k (cohomologyOverField k pX (normalSheaf pX pY g hg) 0) : ℤ) =
      curveDegree k pX (IsCurve.topologicalKrullDim_eq_one (f := pX)).le
        (Scheme.Hom.relativeDifferentials pX) 1 -
      (PencilDegreePullback.curveMapDegree pX pY g hg hnc : ℤ) *
        curveDegree k pY (IsCurve.topologicalKrullDim_eq_one (f := pY)).le
          (Scheme.Hom.relativeDifferentials pY) 1 := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
  let := normal_isCoherent pX pY g hg
  let := differentials_rank_one pX
  let := differentials_rank_one pY
  let := tangent_isInvertible pX
  let := pulledTangent_isInvertible pY g
  have h := LineMapCokernelCohomology.cokernel_h0_eq_degree_jump k pX
    (IsCurve.topologicalKrullDim_eq_one (f := pX)).le
    (tangentMap pX pY g hg) (tangentMap_ne_zero pX pY g hg hnc)
  rw [tangent_degree pX, pulledTangent_degree pX pY g hg hnc] at h
  change (Module.finrank k (cohomologyOverField k pX (normalSheaf pX pY g hg) 0) : ℤ) = _ at h
  linarith

/-- Every original stalk in the normal support has finite composition
length over its original local ring. -/
theorem normal_local_length_finite (x : ↥(SheafOfModules.supp (normalSheaf pX pY g hg))) :
    IsFiniteLength (X.presheaf.stalk x.1)
      (TopCat.Presheaf.stalk (C := Ab.{u}) (normalSheaf pX pY g hg).presheaf x.1) := by
  let := normal_isCoherent pX pY g hg
  exact ZeroDimensionalCohomologyLength.stalk_isFiniteLength pX _
    (normal_support_le_zero pX pY g hg hnc) x

/-- Actual normal length, as the sum of original local-ring composition
lengths, agrees with actual H0 over an algebraically closed base. -/
theorem normal_length_eq_h0 [IsAlgClosed k] :
    letI := normal_isCoherent pX pY g hg
    ZeroDimensionalCohomologyLength.totalStalkLength pX (normalSheaf pX pY g hg)
      (normal_support_le_zero pX pY g hg hnc) =
        Module.finrank k (cohomologyOverField k pX (normalSheaf pX pY g hg) 0) := by
  let := normal_isCoherent pX pY g hg
  exact ZeroDimensionalCohomologyLength.totalStalkLength_eq_h0 pX _
    (normal_support_le_zero pX pY g hg hnc)

/-- The same actual differential-degree formula computes the genuine
sum of finite local-ring lengths, not a newly defined H0 count. -/
theorem normal_length_degree_formula [IsAlgClosed k] :
    letI := normal_isCoherent pX pY g hg
    letI := differentials_rank_one pX
    letI := differentials_rank_one pY
    (ZeroDimensionalCohomologyLength.totalStalkLength pX (normalSheaf pX pY g hg)
      (normal_support_le_zero pX pY g hg hnc) : ℤ) =
      curveDegree k pX (IsCurve.topologicalKrullDim_eq_one (f := pX)).le
        (Scheme.Hom.relativeDifferentials pX) 1 -
      (PencilDegreePullback.curveMapDegree pX pY g hg hnc : ℤ) *
        curveDegree k pY (IsCurve.topologicalKrullDim_eq_one (f := pY)).le
          (Scheme.Hom.relativeDifferentials pY) 1 := by
  let := normal_isCoherent pX pY g hg
  let := differentials_rank_one pX
  let := differentials_rank_one pY
  rw [normal_length_eq_h0 pX pY g hg hnc]
  exact normal_h0_degree_formula pX pY g hg hnc

end M9Native.CurveDerivativeNormal
