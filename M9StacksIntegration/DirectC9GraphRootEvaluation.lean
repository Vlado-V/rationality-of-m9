module

public import M9StacksIntegration.LinePolynomialPicardRoots
public import M9StacksIntegration.CurvePowerGraphSchurPolynomial
public import M9StacksIntegration.DirectC9MovingQuotientClass

/-!
# Literal evaluated roots are the actual normalization and graph lines

The original N and kappa modules are used throughout. Their genuine
Picard identities identify the evaluated linear polynomials with the
same original line caps in the actual line-generated subring. The
self-diagonal term is retained. No Chern or Whitney identity is an input
to this identification of the named lines.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.CurvePower MvPolynomial

universe u

namespace M9Native.DirectC9GraphRootEvaluation

open Stacks.Chow ChowCapWords ChowPicardLineFamily GradedLineCapSubring
open LinePolynomialEvaluation LinePolynomialPicardRoots CurvePowerLinePolynomialTrace
open CurvePowerChowFunctional CurvePowerRootChern CurvePowerSchurPolynomial
open CurvePowerGraphSchurPolynomial CurvePowerFiniteTopPower CurvePowerFiltrationRoots

theorem pointSum_extendZero {R : Type*} [CommRing R] {n : ℕ} (p : Fin n → R) :
    CurvePowerFiltrationRoots.pointSum (extendZero p) n = ∑ i : Fin n, p i := by
  simpa only [pointSum_eq_sum, extendZero_fin] using
    (Fin.sum_univ_eq_sum_range (extendZero p) n).symm

abbrev normalizationPolynomial : MvPolynomial (Letter 9) ℤ :=
  -CurvePowerFiltrationRoots.pointSum (extendZero (pointPolynomial 9)) 9

theorem normalizationPolynomial_linear :
    normalizationPolynomial =
      linearPolynomial (fun i : Fin 9 => (Sum.inl i : Letter 9)) (fun _ => -1) := by
  change -CurvePowerFiltrationRoots.pointSum (extendZero (pointPolynomial 9)) 9 = _
  rw [pointSum_extendZero]
  simp only [linearPolynomial, pointPolynomial, neg_one_zsmul, Finset.sum_neg_distrib]

theorem sum_neg_one_smul {A : Type*} [AddCommGroup A] {I : Type*} [Fintype I] (x : I → A) :
    (∑ i, (-1 : ℤ) • x i) = -∑ i, x i := by
  simp only [neg_one_zsmul, Finset.sum_neg_distrib]

abbrev QuotientIndex (j : Fin 9) := Fin 9 ⊕ (Unit ⊕ Fin (j.val + 1))

def quotientVariables (j : Fin 9) : QuotientIndex j → Letter 9
  | .inl i => .inl i
  | .inr (.inl _) => .inl j
  | .inr (.inr a) => .inr (j, ⟨a.val, by omega⟩)

def quotientWeights (j : Fin 9) : QuotientIndex j → ℤ
  | .inl _ => -1
  | .inr (.inl _) => 17
  | .inr (.inr _) => 1

theorem quotientWeights_value {A : Type*} [AddCommGroup A] (x : Letter 9 → A) (j : Fin 9) :
    (∑ i : QuotientIndex j, quotientWeights j i • x (quotientVariables j i)) =
      -∑ i : Fin 9, x (.inl i) + 17 • x (.inl j) +
        ∑ a : Fin (j.val + 1), x (.inr (j, ⟨a.val, by omega⟩)) := by
  simp [QuotientIndex, Fintype.sum_sum_type, quotientVariables, quotientWeights,
    ofNat_zsmul, Finset.sum_neg_distrib, add_assoc]

abbrev quotientPolynomial (j : Fin 9) : MvPolynomial (Letter 9) ℤ :=
  graphQuotient (extendZero (pointPolynomial 9)) (extendZero₂ (diagonalPolynomial 9)) 9 j.val

theorem quotient_diagonal_sum (j : Fin 9) :
    (∑ a ∈ Finset.range (j.val + 1), extendZero₂ (diagonalPolynomial 9) j.val a) =
      ∑ a : Fin (j.val + 1), diagonalPolynomial 9 j ⟨a.val, by omega⟩ := by
  calc
    (∑ a ∈ Finset.range (j.val + 1), extendZero₂ (diagonalPolynomial 9) j.val a) =
        ∑ a : Fin (j.val + 1), extendZero₂ (diagonalPolynomial 9) j.val a.val :=
      (Fin.sum_univ_eq_sum_range
        (fun a => extendZero₂ (diagonalPolynomial 9) j.val a) (j.val + 1)).symm
    _ = ∑ a : Fin (j.val + 1), diagonalPolynomial 9 j ⟨a.val, by omega⟩ := by
      apply Finset.sum_congr rfl
      intro a ha
      have ha9 : a.val < 9 := by omega
      simp only [extendZero₂, dite_eq_left (And.intro j.isLt ha9)]

theorem quotientPolynomial_linear (j : Fin 9) :
    quotientPolynomial j = linearPolynomial (quotientVariables j) (quotientWeights j) := by
  change -CurvePowerFiltrationRoots.pointSum (extendZero (pointPolynomial 9)) 9 +
    17 * extendZero (pointPolynomial 9) j.val +
      (∑ a ∈ Finset.range (j.val + 1), extendZero₂ (diagonalPolynomial 9) j.val a) = _
  rw [extendZero_fin, pointSum_extendZero, quotient_diagonal_sum]
  simp [linearPolynomial, Fintype.sum_sum_type, quotientVariables, quotientWeights,
    pointPolynomial, diagonalPolynomial, zsmul_eq_mul, Finset.sum_neg_distrib, add_assoc]

variable {k : Type u} [Field k] (C : Over (Spec (.of k))) [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)

abbrev normalizationLine : InvertibleLine (power C 9).left :=
  nativeLine (DirectC9PoincareFamily.inverseNormalizationLine C c₀)
    (DirectC9FamilyDegree.inverseNormalizationLine_isInvertible C c₀)

abbrev quotientLine (j : Fin 9) : InvertibleLine (power C 9).left :=
  nativeLine (DirectC9MovingQuotientClass.movingQuotientLine C c₀ j.val (by omega))
    (DirectC9MovingQuotientClass.movingQuotientLine_isInvertible C c₀ j.val (by omega))

theorem normalizationLine_class :
    actualClass (normalizationLine C c₀) = -DirectC9NormalizationClass.pointSum C c₀ :=
  (actualClass_nativeLine _ _).trans (DirectC9NormalizationClass.inverseNormalizationLine_class C c₀)

theorem quotientLine_class (j : Fin 9) :
    actualClass (quotientLine C c₀ j) =
      -DirectC9NormalizationClass.pointSum C c₀ +
        17 • DirectC9NormalizationClass.pointClassAt C c₀ j +
        ∑ a : Fin (j.val + 1),
          DirectC9MovingQuotientClass.diagonalClassAt C j ⟨a.val, by omega⟩ :=
  (actualClass_nativeLine _ _).trans
    (DirectC9MovingQuotientClass.movingQuotientLine_class C c₀ j.val (by omega))

theorem pointClassAt_eq_letter (i : Fin 9) :
    DirectC9NormalizationClass.pointClassAt C c₀ i = letterClass k C c₀ 9 (.inl i) := rfl

theorem diagonalClassAt_eq_letter (i j : Fin 9) :
    DirectC9MovingQuotientClass.diagonalClassAt C i j = letterClass k C c₀ 9 (.inr (i,j)) := rfl

theorem normalizationLine_class_letters :
    actualClass (normalizationLine C c₀) = -∑ i : Fin 9, letterClass k C c₀ 9 (.inl i) := by
  rw [normalizationLine_class, DirectC9NormalizationClass.pointSum]
  rfl

theorem quotientLine_class_letters (j : Fin 9) :
    actualClass (quotientLine C c₀ j) =
      -∑ i : Fin 9, letterClass k C c₀ 9 (.inl i) +
        17 • letterClass k C c₀ 9 (.inl j) +
        ∑ a : Fin (j.val + 1), letterClass k C c₀ 9 (.inr (j, ⟨a.val, by omega⟩)) := by
  rw [quotientLine_class, DirectC9NormalizationClass.pointSum]
  rfl

theorem normalizationPolynomial_evaluation :
    evaluation (fieldChowSituation k) (power C 9).hom (variableLine k C c₀ 9)
      normalizationPolynomial = lineRoot (fieldChowSituation k) (power C 9).hom
        (normalizationLine C c₀) := by
  rw [normalizationPolynomial_linear]
  apply evaluation_line_of_class_eq (fieldChowSituation k) (power C 9).hom
    (letterClass k C c₀ 9) (fun i : Fin 9 => (Sum.inl i : Letter 9)) (fun _ => -1)
  exact (normalizationLine_class_letters C c₀).trans
    (sum_neg_one_smul (fun i : Fin 9 => letterClass k C c₀ 9 (.inl i))).symm

theorem quotientPolynomial_evaluation (j : Fin 9) :
    evaluation (fieldChowSituation k) (power C 9).hom (variableLine k C c₀ 9)
      (quotientPolynomial j) = lineRoot (fieldChowSituation k) (power C 9).hom
        (quotientLine C c₀ j) := by
  rw [quotientPolynomial_linear]
  apply evaluation_line_of_class_eq (fieldChowSituation k) (power C 9).hom
    (letterClass k C c₀ 9) (quotientVariables j) (quotientWeights j)
  exact (quotientLine_class_letters C c₀ j).trans
    (quotientWeights_value (letterClass k C c₀ 9) j).symm

def quotientLineAt (j : ℕ) : InvertibleLine (power C 9).left :=
  if h : j < 9 then quotientLine C c₀ ⟨j,h⟩ else normalizationLine C c₀

theorem quotientLineAt_of_lt (j : ℕ) (hj : j < 9) :
    quotientLineAt C c₀ j = quotientLine C c₀ ⟨j,hj⟩ := by
  rw [quotientLineAt, dite_eq_left hj]

def graphLines : List (InvertibleLine (power C 9).left) :=
  ((List.range 9).reverse.map (quotientLineAt C c₀)) ++ List.replicate 9 (normalizationLine C c₀)

theorem graphLines_length : (graphLines C c₀).length = 18 := by
  simp only [graphLines, List.length_append, List.length_map, List.length_reverse,
    List.length_range, List.length_replicate]

theorem graphRootPolynomials_evaluation :
    graphRootPolynomials.map
      (evaluation (fieldChowSituation k) (power C 9).hom (variableLine k C c₀ 9)) =
      (graphLines C c₀).map (lineRoot (fieldChowSituation k) (power C 9).hom) := by
  simp only [graphRootPolynomials, graphLines, List.map_append, List.map_map, List.map_replicate]
  congr 1
  · apply List.map_congr_left
    intro j hj
    have hj9 : j < 9 := List.mem_range.mp (List.mem_reverse.mp hj)
    change evaluation (fieldChowSituation k) (power C 9).hom (variableLine k C c₀ 9)
      (quotientPolynomial ⟨j,hj9⟩) =
        lineRoot (fieldChowSituation k) (power C 9).hom (quotientLineAt C c₀ j)
    rw [quotientLineAt_of_lt]
    exact quotientPolynomial_evaluation C c₀ ⟨j,hj9⟩
  · exact congrArg (List.replicate 9) (normalizationPolynomial_evaluation C c₀)

theorem graphSchurPolynomial_evaluation_lines :
    nativeEvaluation (fieldChowSituation k) (power C 9).hom (variableLine k C c₀ 9)
      graphSchurPolynomial =
      inclusion (fieldChowSituation k) (power C 9).hom
        (segreSchurMatrix ((graphLines C c₀).map
          (lineRoot (fieldChowSituation k) (power C 9).hom))).det := by
  rw [graphSchurPolynomial_evaluation, graphRootPolynomials_evaluation]

variable [IsAlgClosed k] [IsVariety k C.hom] (hC : topologicalKrullDim C.left = 1)

include hC

theorem graphLinesSchur_topTrace (hg9 : genus C.hom = 9) :
    GradedCapTopTrace.topTrace k (power C 9).hom 9
      (inclusion (fieldChowSituation k) (power C 9).hom
        (segreSchurMatrix ((graphLines C c₀).map
          (lineRoot (fieldChowSituation k) (power C 9).hom))).det) = 15240960 := by
  rw [← graphSchurPolynomial_evaluation_lines]
  exact graphSchurPolynomial_topTrace k C c₀ hC hg9

theorem graphLinesSchur_ne_zero (hg9 : genus C.hom = 9) :
    inclusion (fieldChowSituation k) (power C 9).hom
      (segreSchurMatrix ((graphLines C c₀).map
        (lineRoot (fieldChowSituation k) (power C 9).hom))).det ≠ 0 := by
  rw [← graphSchurPolynomial_evaluation_lines]
  exact graphSchurPolynomial_operator_ne_zero k C c₀ hC hg9

end M9Native.DirectC9GraphRootEvaluation
