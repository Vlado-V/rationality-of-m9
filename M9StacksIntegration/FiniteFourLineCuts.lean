module

public import M9StacksIntegration.FiniteZeroRegularity
public import M9StacksIntegration.LineTupleTopChern
public import M9StacksIntegration.ChowRegularSectionClass
public import StacksFrontier.AlgebraicGeometry.Chow.DominantPrimeCycle
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ClosedPointResidueField
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegreeClosedSubscheme

/-!
# Genuine four-line-cut fundamental classes, with full finite structure

On an actual smooth pure fourfold over the original field, four actual
sections of the same actual line define a native rank-four tuple.
Finiteness of their FULL simultaneous zero scheme derives native local
regularity without any regular-prefix or transversality assumption.
Stacks 0FA9, genuine Whitney, and the computed actual top coefficient
then give its original own-fundamental push and its actual finite length.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Chow Stacks.Chow.GenuineChern
universe u
namespace M9Native.FiniteFourLineCuts
open ChowCapWords LineTupleZeroScheme

/-- The actual delta-dimension bound of any scheme finite over the
original field, including a nonreduced or empty scheme. -/
theorem finite_deltaDimension_le_zero (K : Type u) [Field K] {Y : Scheme.{u}}
    (t : Y ⟶ Spec (.of K)) [IsFinite t] :
    schemeDeltaDimension (fieldChowSituation K) t ≤ (0 : EInt) := by
  have hz (y : Y) : relativeDimension (fieldChowSituation K).dimensionFunction t y = 0 := by
    have h := relativeDimension_eq_of_finite_residueField
      (fieldChowSituation K).dimensionFunction (𝟙 (fieldChowSituation K).S) t y
      (finite_residueField_of_isClosed t (FiniteZeroRegularity.isClosed_point_of_isFinite K t y))
    have h' : relativeDimension (fieldChowSituation K).dimensionFunction t y =
        (fieldChowSituation K).dimensionFunction (t y) := by
      simpa only [Category.comp_id, relativeDimension_id] using h
    exact h'.trans (fieldChowSituation_dimensionFunction_eq_zero K (t y))
  rw [schemeDeltaDimension_eq_iSup]
  refine iSup_le fun Z => ?_
  change ((relativeDimension (fieldChowSituation K).dimensionFunction t _) : EInt) ≤ 0
  rw [hz]
  exact le_rfl

/-- Smoothness and genuine pure dimension four derive the original
field-Chow dimension bound. -/
theorem smooth_four_deltaDimension_le (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] (hequi : Equidimensional X)
    (hdim : topologicalKrullDim X = 4) :
    schemeDeltaDimension (fieldChowSituation K) f ≤ ((4 : ℤ) : EInt) := by
  have hbase : schemeDeltaDimension (fieldChowSituation K)
      (𝟙 (fieldChowSituation K).S) ≤ (0 : EInt) := by
    rw [schemeDeltaDimension_eq_iSup]
    refine iSup_le fun Z => ?_
    simp only [deltaDimension, relativeDimension_id]
    exact le_rfl
  have h := SectionZeroScheme.schemeDeltaDimension_le_of_flat (fieldChowSituation K)
    (𝟙 (fieldChowSituation K).S) f 4
    (relativeDimension_of_equidimensional K f hequi 4 hdim) hbase
  simpa only [Category.comp_id, Int.zero_add, Nat.cast_ofNat] using h

variable (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f]
    (hequi : Equidimensional X) (hdim : topologicalKrullDim X = 4)
    (L : InvertibleLine X) (s : Fin 4 → Γ(L.1, ⊤))

local instance lineInvertible :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L.1 := L.2

/-- The literal sum ideal of the four original line sections. -/
abbrev fourCutIdeal : X.IdealSheafData := LineSectionIdealSum.ideal L.1 (List.ofFn s)

/-- The literal native successive four-cut immersion has exactly the
rank-four tuple's full dual-evaluation ideal. -/
theorem ordered_cut_ker_eq_tuple_zero :
    (IteratedLineSectionCuts.simultaneousCut L.1 (List.ofFn s)).hom.ker =
      zeroSchemeOfSection X (tupleBundle L 4) (tupleSection L 4 s) :=
  (LineSectionIdealSum.cut_ker L.1 (List.ofFn s)).trans (zeroIdeal_eq L 4 s).symm

variable [IsFinite ((fourCutIdeal L s).subschemeι ≫ f)]

include hequi hdim

/-- The FULL simultaneous-zero cycle, in the original ambient Chow
group, is the fourth native first-Chern cap of the original line. -/
theorem closed_zeroClass_eq_four_caps :
    QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation K) f 0)
      (cycleAssociatedToClosedSubscheme (fieldChowSituation K) f
        (fourCutIdeal L s).subschemeι 0) =
    capPow (fieldChowSituation K) f (lineCap (fieldChowSituation K) f L) 4 4 0
      (by omega) (fundamentalChowClass (fieldChowSituation K) f 4) := by
  have hi : zeroSchemeOfSection X (tupleBundle L 4) (tupleSection L 4 s) =
      fourCutIdeal L s := zeroIdeal_eq L 4 s
  let : IsFinite ((zeroSchemeOfSection X (tupleBundle L 4) (tupleSection L 4 s)).subschemeι ≫ f) := by
    rw [hi]
    infer_instance
  have hreg := FiniteZeroRegularity.rank_four_regular_of_finite_zero K f hequi hdim
    (fieldChowSituation K) f (tupleBundle L 4) (tupleSection L 4 s)
  have h := ChowRegularSectionClass.closed_zeroClass_eq_topCap (fieldChowSituation K) f
    (tupleBundle L 4) 4 (tupleSection L 4 s) 4
    (smooth_four_deltaDimension_le K f hequi hdim)
    (finite_deltaDimension_le_zero K
      ((zeroSchemeOfSection X (tupleBundle L 4) (tupleSection L 4 s)).subschemeι ≫ f)) hreg
  rw [LineTupleTopChern.topCap_eq_four_line_caps] at h
  exact (congrArg (fun J : X.IdealSheafData =>
    QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation K) f 0)
      (cycleAssociatedToClosedSubscheme (fieldChowSituation K) f J.subschemeι 0)) hi).symm.trans h

/-- The own fundamental class of the FULL simultaneous-zero scheme
pushes by its actual closed immersion to the same actual four-cap class. -/
theorem inclusionPush_fundamental_eq_four_caps :
    ChowLineProperPush.properPush (fieldChowSituation K)
      ((fourCutIdeal L s).subschemeι ≫ f) f (fourCutIdeal L s).subschemeι rfl 0
      (fundamentalChowClass (fieldChowSituation K) ((fourCutIdeal L s).subschemeι ≫ f) 0) =
    capPow (fieldChowSituation K) f (lineCap (fieldChowSituation K) f L) 4 4 0
      (by omega) (fundamentalChowClass (fieldChowSituation K) f 4) := by
  have h := closed_zeroClass_eq_four_caps K f hequi hdim L s
  simpa only [ChowLineProperPush.properPush, fundamentalChowClass, fundamentalCycle,
    properChowPushforward_mk, properPushforward_cycleAssociatedToClosedSubscheme_id] using h

/-- The degree of the actual four-cap intersection is the original
finite algebra's dimension; all nilpotent multiplicities are counted. -/
theorem degree_four_caps_eq_finrank [IsProper f] :
    chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K) f
      (IsLocalRing.closedPoint K)
      (capPow (fieldChowSituation K) f (lineCap (fieldChowSituation K) f L) 4 4 0
        (by omega) (fundamentalChowClass (fieldChowSituation K) f 4)) =
      letI : Algebra K Γ((fourCutIdeal L s).subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of K)).inv ≫ ((fourCutIdeal L s).subschemeι ≫ f).appTop).hom.toAlgebra
      (Module.finrank K Γ((fourCutIdeal L s).subscheme, ⊤) : ℤ) := by
  rw [← closed_zeroClass_eq_four_caps K f hequi hdim L s, chowDegree_mk]
  exact cycleDegree_cycleAssociatedToClosedSubscheme_eq_finrank_globalSections K f
    (fourCutIdeal L s) (finite_deltaDimension_le_zero K ((fourCutIdeal L s).subschemeι ≫ f))
    (IsLocalRing.closedPoint K)

end M9Native.FiniteFourLineCuts
