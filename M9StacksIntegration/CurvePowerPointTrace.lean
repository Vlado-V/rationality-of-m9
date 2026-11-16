module

public import M9StacksIntegration.CurvePowerPointCoordinates
public import M9StacksIntegration.CurvePowerPolynomialTrace
public import Mathlib.Algebra.BigOperators.Fin

/-!
# A genuine polynomial trace with point-product value one

The trace is built from the native first-Chern-cap word degree on the
actual curve power. Its value on the product of all coordinate point
variables is the actual recursive graph computation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.CurvePower MvPolynomial

universe u

namespace M9Native.CurvePowerPointTrace

open CurvePowerPolynomialTrace CurvePowerChowFunctional

attribute [local instance] ChowCapDegree.isInvertible_sheaf_of_presheaf
  ChowCapDegreePicard.chosenLine_isInvertible

section Words

variable {α M : Type*} [AddCommGroup M]

def wordExponent (w : List α) : α →₀ ℕ :=
  w.foldr (fun a e => Finsupp.single a 1 + e) 0

def wordPolynomial (w : List α) : MvPolynomial α ℤ := (w.map X).prod

theorem canonicalWord_perm (w : List α) : (word (wordExponent w)).Perm w := by
  induction w with
  | nil => simp [wordExponent, word_zero]
  | cons a w ih =>
      change (word (Finsupp.single a 1 + wordExponent w)).Perm (a :: w)
      exact (word_add_perm _ _).trans (by simpa only [word_single_one,
        List.singleton_append] using List.Perm.cons a ih)

theorem wordPolynomial_eq_monomial (w : List α) :
    wordPolynomial w = monomial (wordExponent w) 1 := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      change X a * wordPolynomial w = monomial (Finsupp.single a 1 + wordExponent w) 1
      rw [ih]
      change monomial (Finsupp.single a 1) 1 * monomial (wordExponent w) 1 = _
      rw [monomial_mul_monomial, one_mul]

theorem trace_wordPolynomial (F : List α → M)
    (hF : ∀ u v, u.Perm v → F u = F v) (w : List α) :
    trace F (wordPolynomial w) = F w := by
  rw [wordPolynomial_eq_monomial, trace_monomial, one_smul,
    hF _ _ (canonicalWord_perm w)]

theorem wordPolynomial_ofFn {m : ℕ} (a : Fin m → α) :
    wordPolynomial (List.ofFn a) = ∏ j, X (a j) := by
  simp only [wordPolynomial, List.map_ofFn, List.prod_ofFn, Function.comp_apply]

end Words

theorem wordDegree_ofFn (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] {m : ℕ}
    (x : Fin m → Stacks.Picard.ofScheme X) :
    wordDegree k f ((List.ofFn x).map chosenLine) =
      ChowCapDegreePicard.capDegreePicard k f x
        (CurveTopChowClass.identityChowClass (Stacks.Chow.fieldChowSituation k) f m) := by
  let C := Stacks.Chow.fieldChowSituation k
  have hOps : List.ofFn (fun j : Fin m =>
      Stacks.Chow.invCap C f (chosenLine (x j)).1) =
        ((List.ofFn x).map chosenLine).map (ChowCapWords.lineCap C f) := by
    simp only [List.map_ofFn, Function.comp_def, ChowCapWords.lineCap]
  unfold wordDegree ChowCapDegreePicard.capDegreePicard ChowCapDegree.capDegree
    ChowCapDegree.iteratedFirstChernCap
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  apply congrArg (Stacks.Chow.chowDegree C
    (Stacks.Chow.fieldChowSituation_dimensionFunction_eq_zero k) f (IsLocalRing.closedPoint k))
  apply Stacks.Chow.chowGroup_eq_of_heq C f
  apply HEq.symm
  apply Stacks.Chow.iteratedChernCapOnChow_heq_of_eq C f hOps 0
  have hd : (m : ℤ) =
      0 + ((((List.ofFn x).map chosenLine).map (ChowCapWords.lineCap C f)).length : ℤ) := by simp
  have hh : ∀ a b : ℤ, a = b →
      HEq (CurveTopChowClass.identityChowClass C f a)
        (CurveTopChowClass.identityChowClass C f b) := by
    rintro a b rfl
    rfl
  exact (Stacks.Chow.chowGroupCast_heq C f _
    (CurveTopChowClass.identityChowClass C f m)).trans (hh _ _ hd)

variable (k : Type u) [Field k] (C : Over (Spec (.of k))) [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)

def actualWordDegree (m : ℕ) (w : List (Letter m)) : ℤ :=
  wordDegree k (power C m).hom ((w.map (letterClass k C c₀ m)).map chosenLine)

theorem actualWordDegree_perm (m : ℕ) (w w' : List (Letter m)) (h : w.Perm w') :
    actualWordDegree k C c₀ m w = actualWordDegree k C c₀ m w' :=
  wordDegree_perm k _ ((h.map _).map _)

def actualTrace (m : ℕ) : MvPolynomial (Letter m) ℤ →+ ℤ :=
  trace (actualWordDegree k C c₀ m)

theorem actualWordDegree_reversePoints [IsAlgClosed k] [IsVariety k C.hom]
    (hC : topologicalKrullDim C.left = 1) (m : ℕ) :
    actualWordDegree k C c₀ m (List.ofFn fun j : Fin m => Sum.inl (Fin.rev j)) = 1 := by
  unfold actualWordDegree
  rw [List.map_ofFn]
  change wordDegree k (power C m).hom
    ((List.ofFn fun j : Fin m => letterClass k C c₀ m (.inl (Fin.rev j))).map chosenLine) = 1
  rw [wordDegree_ofFn]
  exact CurvePowerPointCoordinates.capDegreePicard_reverse_points k C c₀ hC m

theorem actualTrace_pointProduct [IsAlgClosed k] [IsVariety k C.hom]
    (hC : topologicalKrullDim C.left = 1) (m : ℕ) :
    actualTrace k C c₀ m (∏ j : Fin m, X (Sum.inl j : Letter m)) = 1 := by
  have hp : wordPolynomial (List.ofFn fun j : Fin m => (Sum.inl (Fin.rev j) : Letter m)) =
      ∏ j : Fin m, X (Sum.inl j : Letter m) := by
    rw [wordPolynomial_ofFn]
    exact Fintype.prod_equiv Fin.revPerm _ _ (fun _ => rfl)
  rw [← hp]
  exact (trace_wordPolynomial (actualWordDegree k C c₀ m)
    (actualWordDegree_perm k C c₀ m) _).trans
      (actualWordDegree_reversePoints k C c₀ hC m)

end M9Native.CurvePowerPointTrace
