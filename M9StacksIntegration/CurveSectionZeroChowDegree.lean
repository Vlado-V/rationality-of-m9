module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassOfSection
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RiemannRochZeroScheme
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.Algebra.Homology.StrictlyPerfectRestriction

/-!
# Degree of the full zero scheme of an actual line section

The zero ideal is the native evaluation-image ideal, with all nilpotents
retained. A raw global section is read as its genuine compatible section
family. Native regular-section and curve Riemann--Roch theorems then
identify the degree of the actual zero cycle with the actual line degree.
Regularity, finiteness, length and degree are conclusions, never premises.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.Chow

universe u

namespace M9Native.CurveSectionZeroChowDegree

variable {X : Scheme.{u}} (L : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

local instance presheafInvertible :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L :=
  inferInstanceAs (SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)

/-- The actual raw global section as its native compatible section family. -/
def nativeSection : L.sections :=
  Stacks.PresheafOfModules.sectionOfTop L.val s

omit [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] in
theorem nativeSection_eval : (nativeSection L s).eval (op ⊤) = s :=
  Stacks.PresheafOfModules.sectionOfTop_val_top L.val s

/-- The original full zero ideal, rather than its reduction. -/
abbrev zeroIdeal : X.IdealSheafData := zeroSchemeOfSection X L s

/-- The genuine evaluation-image ideal agrees with the native Cartier vocabulary. -/
theorem zeroIdeal_eq_divisor : zeroIdeal L s = Stacks.Divisors.zeroScheme X L s :=
  zeroSchemeOfSection_eq_zeroScheme X L s

theorem zeroIdeal_eq_geometric : zeroIdeal L s = AlgebraicGeometry.zeroScheme X L s := rfl

theorem nativeSection_zero_divisor :
    Stacks.Divisors.zeroScheme X L ((nativeSection L s).eval (op ⊤)) = zeroIdeal L s :=
  (congrArg (Stacks.Divisors.zeroScheme X L) (nativeSection_eval L s)).trans
    (zeroIdeal_eq_divisor L s).symm

theorem nativeSection_zero_geometric :
    AlgebraicGeometry.zeroScheme X L ((nativeSection L s).eval (op ⊤)) = zeroIdeal L s :=
  (congrArg (AlgebraicGeometry.zeroScheme X L) (nativeSection_eval L s)).trans
    (zeroIdeal_eq_geometric L s).symm

theorem nativeSection_regular [IsIntegral X] (hs : s ≠ 0) :
    IsRegularSection X.sheaf.obj X.ringCatSheaf.property (nativeSection L s) := by
  apply isRegularSection_of_eval_top_ne_zero L (nativeSection L s)
  simpa only [nativeSection_eval] using hs

/-- A nonzero actual line section has its genuine effective Cartier zero scheme. -/
theorem zero_cartier [IsIntegral X] (hs : s ≠ 0) :
    Stacks.Divisors.IsEffectiveCartierDivisor (zeroIdeal L s) := by
  have h := (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X L
    (nativeSection L s)).mpr (nativeSection_regular L s hs)
  exact (congrArg (fun I : X.IdealSheafData => Stacks.Divisors.IsEffectiveCartierDivisor I)
    (nativeSection_zero_geometric L s)).mp h

variable (K : Type u) [Field K] (f : X ⟶ Spec (.of K)) [IsProper f]

/-- Finiteness is proved for the SAME full zero scheme. -/
theorem zero_finite [IsIntegral X] (hdim : topologicalKrullDim X ≤ 1) (hs : s ≠ 0) :
    IsFinite ((zeroIdeal L s).subschemeι ≫ f) := by
  have h := isFinite_zeroScheme_of_eval_top_ne_zero K f hdim L (nativeSection L s)
    (by simpa only [nativeSection_eval] using hs)
  exact (congrArg (fun I : X.IdealSheafData => IsFinite (I.subschemeι ≫ f))
    (nativeSection_zero_geometric L s)).mp h

/-- The full native zero-cycle degree equals the original Euler-characteristic
degree of the original line. All regularity and finiteness are derived. -/
theorem cycleDegree_zero_eq_invertibleCurveDegree [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (hs : s ≠ 0) :
    cycleDegree (fieldChowSituation K) f (IsLocalRing.closedPoint K)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation K) f
          (zeroIdeal L s).subschemeι 0) =
      invertibleCurveDegree K f hdim L := by
  have ht : (nativeSection L s).eval (op ⊤) ≠ 0 := by
    simpa only [nativeSection_eval] using hs
  have hzero := degree_zeroCycle_zeroScheme_eq_finrank_cohomologyOverField
    K f hdim L (nativeSection L s) ht
  have hline := invertibleCurveDegree_eq_finrank_cohomologyOverField_zero_zeroScheme
    K f hdim L (nativeSection L s) ht
    (forall_finiteDimensional_cohomologyOverField_unit K f)
  have hcycle := congrArg (fun I : X.IdealSheafData =>
    cycleDegree (fieldChowSituation K) f (IsLocalRing.closedPoint K)
      (cycleAssociatedToClosedSubscheme (fieldChowSituation K) f I.subschemeι 0))
    (nativeSection_zero_divisor L s)
  exact hcycle.symm.trans (hzero.trans hline.symm)

/-- The actual Chow-degree formulation, retaining the literal fundamental
cycle of the original full zero scheme in the original curve. -/
theorem chowDegree_zero_eq_invertibleCurveDegree [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (hs : s ≠ 0) :
    chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
        f (IsLocalRing.closedPoint K)
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation K) f
          (zeroIdeal L s).subschemeι 0)) =
      invertibleCurveDegree K f hdim L :=
  (chowDegree_mk (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
    f (IsLocalRing.closedPoint K) _).trans
    (cycleDegree_zero_eq_invertibleCurveDegree L s K f hdim hs)

/-- Original IsCurve supplies every dimension and integrality hypothesis. -/
theorem chowDegree_zero_eq_invertibleCurveDegree_of_isCurve [IsCurve K f]
    (hs : s ≠ 0) :
    chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
        f (IsLocalRing.closedPoint K)
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation K) f
          (zeroIdeal L s).subschemeι 0)) =
      invertibleCurveDegree K f (IsCurve.topologicalKrullDim_eq_one f).le L :=
  chowDegree_zero_eq_invertibleCurveDegree L s K f
    (IsCurve.topologicalKrullDim_eq_one f).le hs

end M9Native.CurveSectionZeroChowDegree
