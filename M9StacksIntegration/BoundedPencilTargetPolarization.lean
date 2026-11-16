module

public import M9StacksIntegration.PencilProjectiveLineGeometry
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.VeryAmpleLargeDegree
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.VeryAmple

/-! A fixed genuine polarization of the original native projective line.
It is constructed once over the base field, and every later target line
is its actual pullback. The degree-one statement after every extension
of fields is proved by native cohomology base change. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace M9Native.BoundedPencilTargetPolarization
open PencilProjectiveLineGeometry
attribute [local instance] isCurve_projectiveSpaceOver_one

structure PolarizationData (k : Type u) [Field k] where
  line : (Line k).Modules
  [invertible : SheafOfModules.IsInvertible (Line k).presheaf (Line k).ringCatSheaf.property line]
  degree : invertibleCurveDegree k (toBase k) (lineDimension k) line = 1

def polarizationData (k : Type u) [Field k] : PolarizationData k :=
  Classical.choice (by
    let c := Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k 1
    obtain ⟨L, hL, hd⟩ := exists_invertibleCurveDegree_eq_one_of_iso_projectiveLine
      (toBase k) c.iso c.toBase
    exact ⟨{ line := L, invertible := hL, degree := hd }⟩)

def fixedLine (k : Type u) [Field k] : (Line k).Modules := (polarizationData k).line

instance fixedLine_isInvertible (k : Type u) [Field k] :
    SheafOfModules.IsInvertible (Line k).presheaf (Line k).ringCatSheaf.property (fixedLine k) :=
  (polarizationData k).invertible

theorem fixedLine_degree (k : Type u) [Field k] :
    invertibleCurveDegree k (toBase k) (lineDimension k) (fixedLine k) = 1 :=
  (polarizationData k).degree

abbrev situation (k : Type u) [Field k] : CohenMacaulayCurveSituation :=
  let c := Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k 1
  { k := k, X := Line k, f := toBase k,
    dimension_one := IsCurve.topologicalKrullDim_eq_one (k := k) (f := toBase k),
    isIso_globalSections := isIso_globalSections_of_iso_projectiveLine (toBase k) c.iso c.toBase }

theorem target_geometricallyIntegral (k : Type u) [Field k] :
    GeometricallyIntegral (toBase k) := by
  let c := Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k 1
  exact (geometricallyIntegral_genus_degree_one_of_iso_projectiveLine
    (toBase k) c.iso c.toBase).1

theorem fixedLine_isRelativelyVeryAmple (k : Type u) [Field k] :
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple (toBase k) (fixedLine k) := by
  let : GeometricallyIntegral (situation k).f := target_geometricallyIntegral k
  apply (situation k).isRelativelyVeryAmple_of_two_mul_genus_add_one_le (fixedLine k)
  change 2 * (genus (toBase k) : ℤ) + 1 ≤
    invertibleCurveDegree k (toBase k) _ (fixedLine k)
  rw [fixedLine_degree k, genus_line_eq_zero k]
  norm_num

theorem fixedLine_isRelativelyAmple (k : Type u) [Field k] :
    Stacks.RelativeAmple.IsRelativelyAmple (toBase k) (fixedLine k) :=
  Stacks.RelativeAmple.isRelativelyAmple_of_isRelativelyVeryAmple _ _ inferInstance
    (fixedLine_isRelativelyVeryAmple k)

theorem fixedLine_h0_atLeast_two (k : Type u) [Field k] :
    2 ≤ Module.finrank k (cohomologyOverField k (toBase k) (fixedLine k) 0) := by
  let : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (toBase k).appTop) :=
    (situation k).isIso_globalSections
  have h := finrank_sub_finrank_eq_invertibleCurveDegree_add_genus k
    (toBase k) (lineDimension k) (fixedLine k)
  rw [fixedLine_degree k, genus_line_eq_zero k] at h
  omega

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
variable {Y : Scheme.{u}} (q : Y ⟶ Line k) (p : Y ⟶ Spec (.of K))
variable (h : IsPullback q p (toBase k) (Spec.map (CommRingCat.ofHom (algebraMap k K))))

theorem fixedLine_pullback_degree :
    let S := (situation k).ofIsPullback h
    invertibleCurveDegree K S.f S.dimension_one.le
      ((Scheme.Modules.pullback q).obj (fixedLine k)) = 1 :=
  ((situation k).invertibleCurveDegree_ofIsPullback h (fixedLine k)).trans (fixedLine_degree k)

include h in
theorem fixedLine_pullback_h0 :
    Module.finrank K (cohomologyOverField K p
      ((Scheme.Modules.pullback q).obj (fixedLine k)) 0) =
      Module.finrank k (cohomologyOverField k (toBase k) (fixedLine k) 0) := by
  let : (fixedLine k).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank
      k (toBase k) (fixedLine k) 1
  let : (fixedLine k).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  exact finrank_cohomologyOverField_baseChange_field k K q p (toBase k) h (fixedLine k) 0

end M9Native.BoundedPencilTargetPolarization
end
