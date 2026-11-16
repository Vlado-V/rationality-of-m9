module

public import M9StacksIntegration.CurvePowerPointTrace
public import M9StacksIntegration.ChowPicardCapTransport
public import M9StacksIntegration.CurveCapEulerDegree
public import M9StacksIntegration.ChowPicardPairingPushforward

/-! A line on an actual integral curve may be replaced by its actual degree
times an actual point line in every projected Chow-cap word. The remaining
word supplies an arbitrary genuine one-cycle, not a numerical-equivalence
or intersection-form assumption. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.CurvePower

universe u
namespace M9Native.CurvePicardWordDegree

open Stacks.Chow CurveTopChowClass CurvePowerChowFunctional ChowCapWords
open ChowPicardCap

variable (k : Type u) [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [IsProper f]

/-- The actual Picard first-Chern cap, followed by actual zero-cycle degree. -/
def picardCapDegree (x : Stacks.Picard.ofScheme X) :
    chowGroup (fieldChowSituation k) f 1 →+ ℤ :=
  (chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k)
    f (IsLocalRing.closedPoint k)).comp (capFun (fieldChowSituation k) f 0 x)

theorem picardCapDegree_identity (hdim : topologicalKrullDim X ≤ 1)
    (x : Stacks.Picard.ofScheme X) :
    picardCapDegree k f x (identityChowClass (fieldChowSituation k) f 1) =
      invertibleCurveDegreeHom k f hdim x := by
  change chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k)
    f (IsLocalRing.closedPoint k) (curvePicardToChowZero k f x) = _
  exact chowDegree_curvePicardToChowZero k f hdim x

/-- The remaining actual cap word evaluated in the one-cycle grading. -/
def wordTailCycle (tail : List (Stacks.Picard.ofScheme X)) :
    chowGroup (fieldChowSituation k) f 1 :=
  iteratedChernCapOnChow (fieldChowSituation k) f
    ((tail.map chosenLine).map (lineCap (fieldChowSituation k) f)) 1
    (identityChowClass (fieldChowSituation k) f
      (1 + (((tail.map chosenLine).map (lineCap (fieldChowSituation k) f)).length : ℤ)))

theorem wordDegree_cons (x : Stacks.Picard.ofScheme X)
    (tail : List (Stacks.Picard.ofScheme X)) :
    wordDegree k f ((x :: tail).map chosenLine) =
      picardCapDegree k f x (wordTailCycle k f tail) := by
  let C := fieldChowSituation k
  let Os := (tail.map chosenLine).map (lineCap C f)
  let O := lineCap C f (chosenLine x)
  change chowDegree C (fieldChowSituation_dimensionFunction_eq_zero k) f
      (IsLocalRing.closedPoint k)
      (iteratedChernCapOnChow C f (O :: Os) 0
        (identityChowClass C f (0 + ((O :: Os).length : ℤ)))) =
    chowDegree C (fieldChowSituation_dimensionFunction_eq_zero k) f
      (IsLocalRing.closedPoint k)
      (O.capOnChow C f 0
        (iteratedChernCapOnChow C f Os 1
          (identityChowClass C f (1 + (Os.length : ℤ)))))
  apply congrArg
    (chowDegree C (fieldChowSituation_dimensionFunction_eq_zero k) f
      (IsLocalRing.closedPoint k))
  apply iteratedChernCapOnChow_cons_eq C f O Os 0
  have he : (0 : ℤ) + ((O :: Os).length : ℤ) = 1 + (Os.length : ℤ) := by
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    ring
  exact (chowGroupCast_heq C f he (identityChowClass C f _)).symm.trans
    (heq_of_eq (CartierCapDegreeRestriction.identityChowClass_cast C f he))

theorem wordTailCycle_nil :
    wordTailCycle k f [] = identityChowClass (fieldChowSituation k) f 1 := by
  exact chowGroup_eq_of_heq (fieldChowSituation k) f
    (iteratedChernCapOnChow_nil_heq (fieldChowSituation k) f 1 _)

theorem wordDegree_singleton (x : Stacks.Picard.ofScheme X) :
    wordDegree k f ([x].map chosenLine) =
      picardCapDegree k f x (identityChowClass (fieldChowSituation k) f 1) := by
  rw [wordDegree_cons, wordTailCycle_nil]

theorem picardCapDegree_proper {Y : Scheme.{u}}
    (fY : Y ⟶ Spec (.of k)) [IsProper fY] (g : Y ⟶ X) [IsProper g]
    (hg : g ≫ f = fY) (x : Stacks.Picard.ofScheme X)
    (a : chowGroup (fieldChowSituation k) fY 1) :
    picardCapDegree k fY (Stacks.Picard.schemePullbackClass g x) a =
      picardCapDegree k f x
        (properChowPushforward (fieldChowSituation k) fY f g hg 1
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper
            (fieldChowSituation k) fY f g hg 1) a) := by
  simp only [picardCapDegree, AddMonoidHom.comp_apply]
  rw [CurveSingleCapDegree.zeroCycleDegree_proper k f fY g hg]
  exact congrArg
    (chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k)
      f (IsLocalRing.closedPoint k))
    (ChowPicardCapTransport.capFun_proper (fieldChowSituation k) f fY g hg 0 x a)

theorem picardCapDegree_cross_mul [IsIntegral X]
    (hdim : topologicalKrullDim X = 1) (x y : Stacks.Picard.ofScheme X)
    (a : chowGroup (fieldChowSituation k) f 1) :
    picardCapDegree k f x a * invertibleCurveDegreeHom k f hdim.le y =
      invertibleCurveDegreeHom k f hdim.le x * picardCapDegree k f y a := by
  rw [← picardCapDegree_identity k f hdim.le y,
    ← picardCapDegree_identity k f hdim.le x]
  exact addHom_cross_mul (fieldChowSituation k) f 1
    (schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq f
      (n := 1) (by rw [hdim]; rfl))
    (picardCapDegree k f x) (picardCapDegree k f y) a

/-- The degree-one normalization in this generic lemma is discharged for
the actual point line on the original one-fold curve power below. -/
theorem wordDegree_pullback_degree_one [IsIntegral X]
    (hdim : topologicalKrullDim X = 1) (x p : Stacks.Picard.ofScheme X)
    (hp : invertibleCurveDegreeHom k f hdim.le p = 1)
    {Y : Scheme.{u}} (fY : Y ⟶ Spec (.of k)) [IsProper fY]
    (g : Y ⟶ X) [IsProper g] (hg : g ≫ f = fY)
    (tail : List (Stacks.Picard.ofScheme Y)) :
    wordDegree k fY ((Stacks.Picard.schemePullbackClass g x :: tail).map chosenLine) =
      invertibleCurveDegreeHom k f hdim.le x *
        wordDegree k fY ((Stacks.Picard.schemePullbackClass g p :: tail).map chosenLine) := by
  rw [wordDegree_cons, wordDegree_cons,
    picardCapDegree_proper k f fY g hg x,
    picardCapDegree_proper k f fY g hg p]
  simpa only [hp, mul_one] using picardCapDegree_cross_mul k f hdim x p
    (properChowPushforward (fieldChowSituation k) fY f g hg 1
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper
        (fieldChowSituation k) fY f g hg 1) (wordTailCycle k fY tail))

end M9Native.CurvePicardWordDegree
