module

public import M9StacksIntegration.LineFamilyCapWords
public import M9StacksIntegration.CurvePowerPointTrace
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Genuine polynomial evaluation in the actual line-generated cap ring

Polynomial evaluation takes place in the proved commutative subring of
actual line families and is then included in the original operational
cap ring. A monomial is the actual ordered line-family word associated
to its multiplicities.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MvPolynomial

universe u v

namespace M9Native.LinePolynomialEvaluation

open Stacks.Chow ChowCapWords CurvePowerPolynomialTrace CurvePowerPointTrace
open GradedLineCapSubring LineFamilyCapWords

theorem wordExponent_toMultiset {α : Type v} (w : List α) :
    Finsupp.toMultiset (wordExponent w) = (w : Multiset α) := by
  induction w with
  | nil => simp [wordExponent]
  | cons a w ih =>
      simpa [wordExponent, Finsupp.toMultiset_add] using
        congrArg (fun m : Multiset α => ({a} : Multiset α) + m) ih

theorem wordExponent_word {α : Type v} (e : α →₀ ℕ) : wordExponent (word e) = e := by
  classical
  apply (Finsupp.orderIsoMultiset).injective
  change Finsupp.toMultiset (wordExponent (word e)) = Finsupp.toMultiset e
  rw [wordExponent_toMultiset]
  exact Multiset.coe_toList _

theorem wordPolynomial_word {α : Type v} (e : α →₀ ℕ) :
    wordPolynomial (word e) = (monomial e 1 : MvPolynomial α ℤ) := by
  rw [wordPolynomial_eq_monomial, wordExponent_word]

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
  [LocallyOfFiniteType q] {α : Type v}

def evaluation (L : α → InvertibleLine X) : MvPolynomial α ℤ →+* lineSubring C q :=
  MvPolynomial.eval₂Hom (Int.castRingHom _) (fun i => lineRoot C q (L i))

def nativeEvaluation (L : α → InvertibleLine X) :
    MvPolynomial α ℤ →+* GradedCapFamily (chowGroup C q) :=
  (inclusion C q).comp (evaluation C q L)

theorem nativeEvaluation_X (L : α → InvertibleLine X) (i : α) :
    nativeEvaluation C q L (MvPolynomial.X i) = lineFamily C q (L i) := by
  change (GradedLineCapSubring.inclusion C q)
    (MvPolynomial.eval₂Hom (Int.castRingHom (lineSubring C q))
      (fun j => lineRoot C q (L j)) (MvPolynomial.X i)) = _
  rw [MvPolynomial.eval₂Hom_X']
  rfl

theorem nativeEvaluation_wordPolynomial (L : α → InvertibleLine X) (w : List α) :
    nativeEvaluation C q L (wordPolynomial w) = familyWord C q (w.map L) := by
  induction w with
  | nil => simp only [wordPolynomial, List.map_nil, List.prod_nil, map_one, familyWord]
  | cons a w ih =>
      have hw : wordPolynomial (a :: w) = MvPolynomial.X a * wordPolynomial w := by
        simp only [wordPolynomial, List.map_cons, List.prod_cons]
      rw [hw, map_mul, nativeEvaluation_X, ih]
      simp only [familyWord, List.map_cons, List.prod_cons]

theorem nativeEvaluation_monomial (L : α → InvertibleLine X) (e : α →₀ ℕ) (c : ℤ) :
    nativeEvaluation C q L (monomial e c) = c • familyWord C q ((word e).map L) := by
  have hc : (monomial e c : MvPolynomial α ℤ) = c • (monomial e 1) := by
    rw [smul_monomial]
    simp only [smul_eq_mul, mul_one]
  calc
    nativeEvaluation C q L (monomial e c) =
        nativeEvaluation C q L (c • monomial e 1) := congrArg (nativeEvaluation C q L) hc
    _ = c • nativeEvaluation C q L (monomial e 1) :=
      (nativeEvaluation C q L).toAddMonoidHom.map_zsmul _ _
    _ = c • familyWord C q ((word e).map L) := by
      rw [← wordPolynomial_word, nativeEvaluation_wordPolynomial]

theorem nativeEvaluation_monomial_homogeneous (L : α → InvertibleLine X)
    (e : α →₀ ℕ) (c : ℤ) :
    (nativeEvaluation C q L (monomial e c)).IsHomogeneous (word e).length := by
  rw [nativeEvaluation_monomial]
  simpa only [List.length_map] using
    (familyWord_homogeneous C q ((word e).map L)).zsmul c

end M9Native.LinePolynomialEvaluation
