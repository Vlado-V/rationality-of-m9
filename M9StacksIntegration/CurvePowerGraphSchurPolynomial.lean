module

public import M9StacksIntegration.CurvePowerSchurPolynomial

/-!
# The literal moving-graph Schur polynomial has nonzero actual degree

The roots retain every self-diagonal variable. Only after passing to
the genuine trace-radical quotient is its actual degree used to compare
the roots with the computed moving-root Schur class. No equality of
Picard self-diagonal and point classes is asserted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.CurvePower MvPolynomial

universe u

namespace M9Native.CurvePowerGraphSchurPolynomial

open CurvePowerChowFunctional CurvePowerPointTrace CurvePowerRootSums
open CurvePowerRootChern CurvePowerTopPower CurvePowerFiniteTopPower
open CurvePowerRootFunctoriality CurvePowerFiltrationRoots CurvePowerSchurPolynomial
open CurvePowerActualTraceRelations CurvePowerActualTraceNormalization
open CurvePowerLinePolynomialTrace LinePolynomialEvaluation GradedCapTopTrace

/-- Literal quotient lines in reverse graph order followed by the nine
normalization lines. The self variable is included in each finite sum. -/
def graphRootPolynomials : List (MvPolynomial (Letter 9) ℤ) :=
  ((List.range 9).reverse.map
    (graphQuotient (extendZero (pointPolynomial 9))
      (extendZero₂ (diagonalPolynomial 9)) 9)) ++
    List.replicate 9 (-pointSum (extendZero (pointPolynomial 9)) 9)

def graphSchurPolynomial : MvPolynomial (Letter 9) ℤ :=
  (segreSchurMatrix graphRootPolynomials).det

theorem graphSchurPolynomial_evaluation (D : Stacks.Chow.ChowSituation.{u})
    {Y : Scheme.{u}} (q : Y ⟶ D.S) [LocallyOfFiniteType q]
    (L : Letter 9 → ChowCapWords.InvertibleLine Y) :
    nativeEvaluation D q L graphSchurPolynomial =
      GradedLineCapSubring.inclusion D q
        (segreSchurMatrix (graphRootPolynomials.map (evaluation D q L))).det := by
  change GradedLineCapSubring.inclusion D q
    (evaluation D q L graphSchurPolynomial) = _
  rw [graphSchurPolynomial, map_segreSchurDet]

variable (k : Type u) [Field k] [IsAlgClosed k]
  (C : Over (Spec (.of k))) [IsVariety k C.hom] [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)
  (hC : topologicalKrullDim C.left = 1)

include hC

theorem quotientMap_graphRoots (hg9 : genus C.hom = 9) :
    graphRootPolynomials.map (quotientMap k C c₀ 9) =
      roots 9 (extendZero (point k C c₀ 9))
        (boundary (extendZero₂ (reducedDiagonal k C c₀ 9))) 9 := by
  let p := extendZero (point k C c₀ 9)
  let d := extendZero₂ (diagonal k C c₀ 9)
  let b := extendZero₂ (reducedDiagonal k C c₀ 9)
  let Q := quotientMap k C c₀ 9
  have hp : (fun i => Q (extendZero (pointPolynomial 9) i)) = p := by
    rw [map_extendZero]
    rfl
  have hd : (fun i j => Q (extendZero₂ (diagonalPolynomial 9) i j)) = d := by
    rw [map_extendZero₂]
    rfl
  have hgraph : (fun j => Q (graphQuotient (extendZero (pointPolynomial 9))
      (extendZero₂ (diagonalPolynomial 9)) 9 j)) = graphQuotient p d 9 := by
    funext j
    rw [map_graphQuotient, hp, hd]
  have hnorm : Q (-pointSum (extendZero (pointPolynomial 9)) 9) = -pointSum p 9 := by
    calc
      Q (-pointSum (extendZero (pointPolynomial 9)) 9) =
          -Q (pointSum (extendZero (pointPolynomial 9)) 9) :=
        Q.toAddMonoidHom.map_neg _
      _ = -pointSum (fun i => Q (extendZero (pointPolynomial 9) i)) 9 :=
        congrArg Neg.neg (map_pointSum Q (extendZero (pointPolynomial 9)) 9)
      _ = -pointSum p 9 := congrArg (fun v => -pointSum v 9) hp
  have hmap : graphRootPolynomials.map Q =
      ((List.range 9).reverse.map (graphQuotient p d 9)) ++
        List.replicate 9 (-pointSum p 9) := by
    simp only [graphRootPolynomials, List.map_append, List.map_map, List.map_replicate]
    change ((List.range 9).reverse.map (fun j => Q (graphQuotient
      (extendZero (pointPolynomial 9)) (extendZero₂ (diagonalPolynomial 9)) 9 j))) ++
        List.replicate 9 (Q (-pointSum (extendZero (pointPolynomial 9)) 9)) = _
    rw [hgraph, hnorm]
  have hself : ∀ j, j < 9 → d j j = -16 * p j := by
    intro j hj
    simpa only [d, p, extendZero₂, extendZero,
      dite_eq_left (And.intro hj hj), dite_eq_left hj] using
      diagonal_self_genus_nine k C c₀ hC hg9 9 ⟨j,hj⟩
  have hother : ∀ i j, i < j → j < 9 → d j i = b i j + p i + p j := by
    intro i j hij hj
    have hi : i < 9 := lt_trans hij hj
    have he : diagonal k C c₀ 9 ⟨j,hj⟩ ⟨i,hi⟩ =
        reducedDiagonal k C c₀ 9 ⟨i,hi⟩ ⟨j,hj⟩ +
          point k C c₀ 9 ⟨i,hi⟩ + point k C c₀ 9 ⟨j,hj⟩ := by
      rw [diagonal_swap k C c₀ 9 ⟨j,hj⟩ ⟨i,hi⟩]
      unfold reducedDiagonal CurvePowerDiagonalAlgebra.reducedDiagonal
      ring
    simpa only [d, b, p, extendZero₂, extendZero,
      dite_eq_left (And.intro hj hi), dite_eq_left (And.intro hi hj),
      dite_eq_left hi, dite_eq_left hj] using he
  exact hmap.trans (roots_nine_eq_actual_factor_shape p b d hself hother).symm

theorem quotientMap_graphSchurPolynomial (hg9 : genus C.hom = 9) :
    quotientMap k C c₀ 9 graphSchurPolynomial =
      CurvePowerActualSchurTrace.actualSchur k C c₀ := by
  rw [graphSchurPolynomial, map_segreSchurDet, quotientMap_graphRoots k C c₀ hC hg9]
  rfl

theorem graphSchurPolynomial_actualTrace (hg9 : genus C.hom = 9) :
    actualTrace k C c₀ 9 graphSchurPolynomial = 15240960 := by
  have h := CurvePowerActualSchurTrace.actualSchur_trace k C c₀ hC hg9
  rw [← quotientMap_graphSchurPolynomial k C c₀ hC hg9] at h
  exact h

theorem graphSchurPolynomial_topTrace (hg9 : genus C.hom = 9) :
    topTrace k (power C 9).hom 9
      (nativeEvaluation (Stacks.Chow.fieldChowSituation k) (power C 9).hom
        (variableLine k C c₀ 9) graphSchurPolynomial) = 15240960 :=
  (actualTrace_eq_topTrace_evaluation k C c₀ hC 9 graphSchurPolynomial).symm.trans
    (graphSchurPolynomial_actualTrace k C c₀ hC hg9)

theorem graphSchurPolynomial_operator_ne_zero (hg9 : genus C.hom = 9) :
    nativeEvaluation (Stacks.Chow.fieldChowSituation k) (power C 9).hom
      (variableLine k C c₀ 9) graphSchurPolynomial ≠ 0 := by
  intro he
  have ht := graphSchurPolynomial_topTrace k C c₀ hC hg9
  rw [he, map_zero] at ht
  norm_num at ht

theorem graphSchur_image_topTrace (hg9 : genus C.hom = 9) :
    topTrace k (power C 9).hom 9
      (GradedLineCapSubring.inclusion (Stacks.Chow.fieldChowSituation k) (power C 9).hom
        (segreSchurMatrix (graphRootPolynomials.map
          (evaluation (Stacks.Chow.fieldChowSituation k) (power C 9).hom
            (variableLine k C c₀ 9)))).det) = 15240960 := by
  rw [← graphSchurPolynomial_evaluation]
  exact graphSchurPolynomial_topTrace k C c₀ hC hg9

theorem graphSchur_image_ne_zero (hg9 : genus C.hom = 9) :
    GradedLineCapSubring.inclusion (Stacks.Chow.fieldChowSituation k) (power C 9).hom
      (segreSchurMatrix (graphRootPolynomials.map
        (evaluation (Stacks.Chow.fieldChowSituation k) (power C 9).hom
          (variableLine k C c₀ 9)))).det ≠ 0 := by
  rw [← graphSchurPolynomial_evaluation]
  exact graphSchurPolynomial_operator_ne_zero k C c₀ hC hg9

end M9Native.CurvePowerGraphSchurPolynomial
