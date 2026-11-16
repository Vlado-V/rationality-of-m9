module

public import M9StacksIntegration.CurveSingleCapDegree
public import StacksFrontier.AlgebraicGeometry.Picard.CurveChowZero
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.CurveDeltaDimension

/-!
# Actual curve-degree replacement in projected Chern-cap pairings

The degree here is the native Euler-characteristic degree of an actual
invertible module on the actual curve. Its comparison with the native
Chow cap is the proved rank-one Riemann--Roch identity, not a numerical
equivalence premise. The projection comparison then applies to every
actual one-cycle obtained from any remaining intersections upstairs.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.CurveCapEulerDegree

open Stacks.Chow CurveTopChowClass CurveSingleCapDegree

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

theorem isInvertible_presheaf_of_sheaf (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L := hL

attribute [local instance] isInvertible_presheaf_of_sheaf

theorem singleCapDegree_identity_eq_invertibleCurveDegree
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    singleCapDegree k f L (identityChowClass (fieldChowSituation k) f 1) =
      @invertibleCurveDegree k _ X f _ hdim L hL := by
  change chowDegree (fieldChowSituation k)
    (fieldChowSituation_dimensionFunction_eq_zero k) f (IsLocalRing.closedPoint k)
    (invertibleCurveChowZeroClass k f L) = _
  exact chowDegree_invertibleCurveChowZeroClass k f hdim L

section IntegralCurve

variable [IsIntegral X] (hone : topologicalKrullDim X = 1) (L M : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]

include hone

theorem singleCapDegree_cross_mul_degrees (a : chowGroup (fieldChowSituation k) f 1) :
    singleCapDegree k f L a * invertibleCurveDegree k f hone.le M =
      invertibleCurveDegree k f hone.le L * singleCapDegree k f M a := by
  rw [← singleCapDegree_identity_eq_invertibleCurveDegree k f hone.le M,
    ← singleCapDegree_identity_eq_invertibleCurveDegree k f hone.le L]
  exact singleCapDegree_cross_mul k f
    (schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq f
      (n := 1) (by rw [hone]; rfl)) L M a

theorem pullback_singleCapDegree_cross_mul_degrees {Y : Scheme.{u}}
    (fY : Y ⟶ Spec (.of k)) [IsProper fY] (g : Y ⟶ X) [IsProper g]
    (hg : g ≫ f = fY) (a : chowGroup (fieldChowSituation k) fY 1) :
    singleCapDegree k fY ((Scheme.Modules.pullback g).obj L) a *
        invertibleCurveDegree k f hone.le M =
      invertibleCurveDegree k f hone.le L *
        singleCapDegree k fY ((Scheme.Modules.pullback g).obj M) a := by
  rw [singleCapDegree_proper k f fY g hg L, singleCapDegree_proper k f fY g hg M]
  exact singleCapDegree_cross_mul_degrees k f hone L M _

theorem singleCapDegree_zero_of_degree_zero
    (hL : invertibleCurveDegree k f hone.le L = 0)
    (a : chowGroup (fieldChowSituation k) f 1) : singleCapDegree k f L a = 0 := by
  apply singleCapDegree_zero_of_identity_zero k f
    (schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq f
      (n := 1) (by rw [hone]; rfl)) L
  exact (singleCapDegree_identity_eq_invertibleCurveDegree k f hone.le L).trans hL

theorem pullback_singleCapDegree_zero_of_degree_zero {Y : Scheme.{u}}
    (fY : Y ⟶ Spec (.of k)) [IsProper fY] (g : Y ⟶ X) [IsProper g]
    (hg : g ≫ f = fY) (hL : invertibleCurveDegree k f hone.le L = 0)
    (a : chowGroup (fieldChowSituation k) fY 1) :
    singleCapDegree k fY ((Scheme.Modules.pullback g).obj L) a = 0 := by
  rw [singleCapDegree_proper k f fY g hg L]
  exact singleCapDegree_zero_of_degree_zero k f hone L hL _

theorem pullback_singleCapDegree_eq_degree_mul_of_degree_one {Y : Scheme.{u}}
    (fY : Y ⟶ Spec (.of k)) [IsProper fY] (g : Y ⟶ X) [IsProper g]
    (hg : g ≫ f = fY) (hM : invertibleCurveDegree k f hone.le M = 1)
    (a : chowGroup (fieldChowSituation k) fY 1) :
    singleCapDegree k fY ((Scheme.Modules.pullback g).obj L) a =
      invertibleCurveDegree k f hone.le L *
        singleCapDegree k fY ((Scheme.Modules.pullback g).obj M) a := by
  simpa only [hM, mul_one] using
    pullback_singleCapDegree_cross_mul_degrees k f hone L M fY g hg a

end IntegralCurve

end M9Native.CurveCapEulerDegree
