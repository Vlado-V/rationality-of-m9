module

public import M9StacksIntegration.BoundedPencilGraphPolynomial
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ContractedDegree
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFibreEulerCharacteristicUnconditional

/-!
# Honest degree converse for the actual graph polarization

The source line is the actual degree-forty-eight embedding line, with no
identification with an arbitrary chosen curve line. The Euler polynomial
of its tensor with the pulled degree-one target line determines the
native function-field degree, and positivity excludes constant maps.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
open Stacks.RelativeVeryAmple

universe u

namespace M9Native.PolarizedCoverGraphDegree

open PencilProjectiveLineGeometry BoundedPencilTargetPolarization BoundedPencilGraphPolynomial
attribute [local instance] isCurve_projectiveSpaceOver_one

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
  (g : X ⟶ Line k) (hg : g ≫ toBase k = f)
  (N : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
  (M : (Line k).Modules)
  [SheafOfModules.IsInvertible (Line k).presheaf (Line k).ringCatSheaf.2 M]

local instance targetPullbackInvertible :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((Scheme.Modules.pullback g).obj M) :=
  Stacks.InvertiblePullback.isInvertibleModule_pullback g M

/-- The literal original source line tensored with the pulled target line. -/
def graphLine : X.Modules :=
  tensorModules X N ((Scheme.Modules.pullback g).obj M)

instance graphLine_isInvertible :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (graphLine g N M) := by
  let := Stacks.InvertiblePullback.isInvertibleModule_pullback g M
  dsimp only [graphLine]
  infer_instance

/-- Integer powers of the actual graph line, with the original field action. -/
def graphPower (m : ℤ) : X.Modules :=
  Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 (graphLine g N M) m

instance graphPower_isInvertible (m : ℤ) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (graphPower g N M m) :=
  Stacks.SheafOfModules.Invertible.tensorPower_isInvertible _ _ _ m

/-- The genuine graph-line degree on the original source, using its
actual degree-forty-eight polarization and the native map degree. -/
theorem graphLine_degree (hdim : topologicalKrullDim X ≤ 1)
    (hN : invertibleCurveDegree k f hdim N = 48)
    (hM : invertibleCurveDegree k (toBase k) (lineDimension k) M = 1)
    (hnc : ¬ ∃ y : Line k, ∀ x : X, g.base x = y) :
    invertibleCurveDegree k f hdim (graphLine g N M) =
      48 + (PencilDegreePullback.curveMapDegree f (toBase k) g hg hnc : ℤ) := by
  exact (invertibleCurveDegree_tensorSheaf_eq_add k f hdim N
    ((Scheme.Modules.pullback g).obj M)).trans
      (congrArg₂ (· + ·) hN
        (PencilDegreePullback.pullback_degree_eq_curveMapDegree f (toBase k)
          hdim (lineDimension k) g hg hnc M hM))

/-- The actual graph Euler polynomial holds at EVERY integer twist,
without identifying the source embedding line with an arbitrary line. -/
theorem graphPower_euler (hdim : topologicalKrullDim X ≤ 1)
    (hgen : genus f = 9) (hN : invertibleCurveDegree k f hdim N = 48)
    (hM : invertibleCurveDegree k (toBase k) (lineDimension k) M = 1)
    (hnc : ¬ ∃ y : Line k, ∀ x : X, g.base x = y) (m : ℤ) :
    ProperFlatFibreEulerCharacteristic.eulerSum k f (graphPower g N M m) =
      graphPolynomial (PencilDegreePullback.curveMapDegree f (toBase k) g hg hnc) m := by
  have hp := invertibleCurveDegree_tensorPower_eq_mul k f hdim (graphLine g N M)
    (@invertibleCurveDegree_tensorSheaf_eq_add k _ X f _ hdim) m
  change invertibleCurveDegree k f hdim (graphPower g N M m) =
    m * invertibleCurveDegree k f hdim (graphLine g N M) at hp
  rw [graphLine_degree f g hg N M hdim hN hM hnc] at hp
  have hO := eulerCharacteristic_unit_eq_one_sub_genus k f hdim
  change ProperFlatFibreEulerCharacteristic.eulerSum k f
    (SheafOfModules.unit X.ringCatSheaf) = 1 - (genus f : ℤ) at hO
  change ProperFlatFibreEulerCharacteristic.eulerSum k f (graphPower g N M m) -
    ProperFlatFibreEulerCharacteristic.eulerSum k f (SheafOfModules.unit X.ringCatSheaf) = _ at hp
  rw [hO, hgen] at hp
  dsimp only [graphPolynomial]
  have hr : (1 : ℤ) - (9 : ℕ) = -8 := by norm_num
  rw [hr] at hp
  nlinarith only [hp]

/-- Even the first twist of the actual graph Euler polynomial determines
the actual degree of the pulled target line. -/
theorem pullbackDegree_of_graphEuler (hdim : topologicalKrullDim X ≤ 1)
    (hgen : genus f = 9) (hN : invertibleCurveDegree k f hdim N = 48) (d : ℕ)
    (hχ : ProperFlatFibreEulerCharacteristic.eulerSum k f (graphLine g N M) =
      graphPolynomial d 1) :
    invertibleCurveDegree k f hdim ((Scheme.Modules.pullback g).obj M) = d := by
  let := Stacks.InvertiblePullback.isInvertibleModule_pullback g M
  have hdeg := invertibleCurveDegree_tensorSheaf_eq_add k f hdim N
    ((Scheme.Modules.pullback g).obj M)
  have hO := eulerCharacteristic_unit_eq_one_sub_genus k f hdim
  change ProperFlatFibreEulerCharacteristic.eulerSum k f
      (SheafOfModules.unit X.ringCatSheaf) = 1 - (genus f : ℤ) at hO
  change ProperFlatFibreEulerCharacteristic.eulerSum k f (graphLine g N M) -
      ProperFlatFibreEulerCharacteristic.eulerSum k f
        (SheafOfModules.unit X.ringCatSheaf) = _ at hdeg
  rw [hχ, hO, hgen, hN] at hdeg
  dsimp only [graphPolynomial] at hdeg
  have hr : (1 : ℤ) - (9 : ℕ) = -8 := by norm_num
  rw [hr] at hdeg
  simp only [mul_one] at hdeg
  linarith only [hdeg]

/-- A positive graph-degree coefficient excludes an actual constant map;
the native zero-degree theorem for a one-point image supplies the contradiction. -/
theorem nonconstant_of_graphEuler (hdim : topologicalKrullDim X ≤ 1)
    (hgen : genus f = 9) (hN : invertibleCurveDegree k f hdim N = 48) (d : ℕ) (hd : 0 < d)
    (hχ : ProperFlatFibreEulerCharacteristic.eulerSum k f (graphLine g N M) =
      graphPolynomial d 1) : ¬ ∃ y : Line k, ∀ x : X, g.base x = y := by
  rintro ⟨y,hy⟩
  have hzero := invertibleCurveDegree_pullback_eq_zero_of_forall_eq k f hdim
    g M y hy
  have heq := pullbackDegree_of_graphEuler f g N M hdim hgen hN d hχ
  have hpos : (0 : ℤ) < (d : ℤ) := Int.natCast_pos.mpr hd
  omega

/-- Actual graph Euler membership with coefficient `d>0` gives a genuine
nonconstant map of native function-field degree exactly `d`. -/
theorem exists_nativeDegree_eq_of_graphEuler (hdim : topologicalKrullDim X ≤ 1)
    (hgen : genus f = 9) (hN : invertibleCurveDegree k f hdim N = 48)
    (hM : invertibleCurveDegree k (toBase k) (lineDimension k) M = 1) (d : ℕ) (hd : 0 < d)
    (hχ : ProperFlatFibreEulerCharacteristic.eulerSum k f (graphLine g N M) =
      graphPolynomial d 1) :
    ∃ hnc : ¬ ∃ y : Line k, ∀ x : X, g.base x = y,
      PencilDegreePullback.curveMapDegree f (toBase k) g hg hnc = d := by
  have hn := nonconstant_of_graphEuler f g N M hdim hgen hN d hd hχ
  refine ⟨hn, ?_⟩
  have heq := pullbackDegree_of_graphEuler f g N M hdim hgen hN d hχ
  have hdeg := PencilDegreePullback.pullback_degree_eq_curveMapDegree f (toBase k)
    hdim (lineDimension k) g hg hn M hM
  exact_mod_cast hdeg.symm.trans heq

end M9Native.PolarizedCoverGraphDegree
end
