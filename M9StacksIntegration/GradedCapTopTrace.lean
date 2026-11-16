module

public import M9StacksIntegration.LineFamilyCapWords
public import M9StacksIntegration.CurvePowerPointTrace

/-!
# The actual top-degree trace of operational cap families

The trace applies the selected actual homogeneous component to the
actual fundamental Chow class and takes the actual proper zero-cycle
degree. Its comparison with a line word uses the proved native cap
word equality. Other word lengths vanish by actual homogeneity and
the grading of the integral fundamental class.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.GradedCapTopTrace

open Stacks.Chow ChowCapWords CurveTopChowClass CurvePowerChowFunctional
open LineFamilyCapWords

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

def topTrace (N : ℕ) : GradedCapFamily (chowGroup (fieldChowSituation k) f) →+ ℤ :=
  let C := fieldChowSituation k
  let deg := chowDegree C (fieldChowSituation_dimensionFunction_eq_zero k) f (IsLocalRing.closedPoint k)
  let a := identityChowClass C f (N : ℤ)
  AddMonoidHom.mk' (fun A => deg (gradedDegreeCast (chowGroup C f)
    (show (N : ℤ) - (N : ℤ) = 0 by omega) (A (N : ℤ) N a))) fun A B => by
      change deg (gradedDegreeCast (chowGroup C f) _ (A (N : ℤ) N a + B (N : ℤ) N a)) =
        deg (gradedDegreeCast (chowGroup C f) _ (A (N : ℤ) N a)) +
        deg (gradedDegreeCast (chowGroup C f) _ (B (N : ℤ) N a))
      rw [map_add, map_add]

theorem topTrace_apply (N : ℕ) (A : GradedCapFamily (chowGroup (fieldChowSituation k) f)) :
    topTrace k f N A =
      chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction_eq_zero k) f
        (IsLocalRing.closedPoint k)
        (gradedDegreeCast (chowGroup (fieldChowSituation k) f)
          (show (N : ℤ) - (N : ℤ) = 0 by omega)
          (A (N : ℤ) N (identityChowClass (fieldChowSituation k) f (N : ℤ)))) := rfl

theorem topTrace_familyWord_length (Ls : List (InvertibleLine X)) :
    topTrace k f Ls.length (familyWord (fieldChowSituation k) f Ls) = wordDegree k f Ls := by
  let C := fieldChowSituation k
  rw [topTrace_apply]
  unfold wordDegree
  apply congrArg (chowDegree C (fieldChowSituation_dimensionFunction_eq_zero k) f
    (IsLocalRing.closedPoint k))
  apply chowGroup_eq_of_heq C f
  refine (gradedDegreeCast_heq _ _).trans ?_
  have hg : (Ls.length : ℤ) = 0 + ((Ls.map (lineCap C f)).length : ℤ) := by simp
  have hh : ∀ a b : ℤ, a = b → HEq (identityChowClass C f a) (identityChowClass C f b) := by
    rintro a b rfl
    rfl
  exact familyWord_apply_heq C f Ls (show (Ls.length : ℤ) - (Ls.length : ℤ) = 0 by omega)
    (hh _ _ hg)

theorem topTrace_familyWord_of_ne (N : ℕ) (Ls : List (InvertibleLine X))
    (h : N ≠ Ls.length) : topTrace k f N (familyWord (fieldChowSituation k) f Ls) = 0 := by
  rw [topTrace_apply, familyWord_homogeneous (fieldChowSituation k) f Ls (N : ℤ) N h]
  simp only [AddMonoidHom.zero_apply, map_zero]

theorem wordDegree_eq_zero_of_genericDimension_ne [IsIntegral X]
    (Ls : List (InvertibleLine X))
    (h : relativeDimension (fieldChowSituation k).dimensionFunction f (genericPoint X) ≠ Ls.length) :
    wordDegree k f Ls = 0 := by
  let C := fieldChowSituation k
  unfold wordDegree
  have hz : identityChowClass C f (0 + ((Ls.map (lineCap C f)).length : ℤ)) = 0 :=
    identityChowClass_eq_zero_of_genericDimension_ne C f _
      (by simpa only [List.length_map, zero_add] using h)
  rw [hz, map_zero, map_zero]

theorem topTrace_familyWord [IsIntegral X] (N : ℕ)
    (hN : relativeDimension (fieldChowSituation k).dimensionFunction f (genericPoint X) = N)
    (Ls : List (InvertibleLine X)) :
    topTrace k f N (familyWord (fieldChowSituation k) f Ls) = wordDegree k f Ls := by
  by_cases h : Ls.length = N
  · subst N
    exact topTrace_familyWord_length k f Ls
  · have hdim : relativeDimension (fieldChowSituation k).dimensionFunction f
        (genericPoint X) ≠ Ls.length := by
      rw [hN]
      exact_mod_cast Ne.symm h
    exact (topTrace_familyWord_of_ne k f N Ls (Ne.symm h)).trans
      (wordDegree_eq_zero_of_genericDimension_ne k f Ls hdim).symm

end M9Native.GradedCapTopTrace
