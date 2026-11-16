module

public import M9StacksIntegration.CurvePowerActualSchurTrace
public import M9StacksIntegration.CurvePowerRootFunctoriality
public import M9StacksIntegration.CurvePowerLinePolynomialTrace

/-!
# A concrete Schur polynomial with a nonzero actual cap operator

The polynomial is lifted explicitly from coordinate points and reduced
diagonals. Its genuine quotient image is the already computed Schur
class. The proved actual trace equality then gives its original Chow
cap operator degree and nonvanishing. No faithfulness premise is used.
Identification with the Chern operator of the actual bundle remains a
separate geometric theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.CurvePower MvPolynomial

universe u

namespace M9Native.CurvePowerSchurPolynomial

open CurvePowerChowFunctional CurvePowerPointTrace CurvePowerRootSums
open CurvePowerRootChern CurvePowerTopPower CurvePowerFiniteTopPower
open CurvePowerRootFunctoriality CurvePowerActualTraceRelations
open CurvePowerLinePolynomialTrace LinePolynomialEvaluation GradedCapTopTrace

def pointPolynomial (n : ℕ) (i : Fin n) : MvPolynomial (Letter n) ℤ := X (.inl i)

def diagonalPolynomial (n : ℕ) (i j : Fin n) : MvPolynomial (Letter n) ℤ := X (.inr (i,j))

def reducedDiagonalPolynomial (n : ℕ) (i j : Fin n) : MvPolynomial (Letter n) ℤ :=
  diagonalPolynomial n i j - pointPolynomial n i - pointPolynomial n j

def rootPolynomials : List (MvPolynomial (Letter 9) ℤ) :=
  roots 9 (extendZero (pointPolynomial 9))
    (boundary (extendZero₂ (reducedDiagonalPolynomial 9))) 9

def schurPolynomial : MvPolynomial (Letter 9) ℤ :=
  (segreSchurMatrix rootPolynomials).det

section Actual

variable (k : Type u) [Field k]
  (C : Over (Spec (.of k))) [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)

def quotientMap (n : ℕ) : MvPolynomial (Letter n) ℤ →+* TraceQuotient k C c₀ n :=
  Ideal.Quotient.mk (PolynomialTraceRelations.radical (actualWordDegree k C c₀ n))

theorem quotientMap_point (n : ℕ) (i : Fin n) :
    quotientMap k C c₀ n (pointPolynomial n i) = point k C c₀ n i := rfl

theorem quotientMap_diagonal (n : ℕ) (i j : Fin n) :
    quotientMap k C c₀ n (diagonalPolynomial n i j) = diagonal k C c₀ n i j := rfl

theorem quotientMap_reducedDiagonal (n : ℕ) (i j : Fin n) :
    quotientMap k C c₀ n (reducedDiagonalPolynomial n i j) =
      reducedDiagonal k C c₀ n i j := by
  let Q := (quotientMap k C c₀ n).toAddMonoidHom
  change Q ((diagonalPolynomial n i j - pointPolynomial n i) - pointPolynomial n j) = _
  rw [Q.map_sub, Q.map_sub]
  rfl

theorem quotientMap_roots :
    rootPolynomials.map (quotientMap k C c₀ 9) =
      roots 9 (extendZero (point k C c₀ 9))
        (boundary (extendZero₂ (reducedDiagonal k C c₀ 9))) 9 := by
  have hp : (fun i : Fin 9 => quotientMap k C c₀ 9 (pointPolynomial 9 i)) =
      point k C c₀ 9 := by funext i; rfl
  have hd : (fun i j : Fin 9 =>
      quotientMap k C c₀ 9 (reducedDiagonalPolynomial 9 i j)) =
      reducedDiagonal k C c₀ 9 := by
    funext i j
    exact quotientMap_reducedDiagonal k C c₀ 9 i j
  rw [rootPolynomials, map_roots, map_extendZero, map_boundary, map_extendZero₂, hp, hd]

theorem quotientMap_schurPolynomial :
    quotientMap k C c₀ 9 schurPolynomial = CurvePowerActualSchurTrace.actualSchur k C c₀ := by
  rw [schurPolynomial, map_segreSchurDet, quotientMap_roots]
  rfl

variable [IsAlgClosed k] [IsVariety k C.hom] (hC : topologicalKrullDim C.left = 1)

include hC

theorem schurPolynomial_actualTrace (hg9 : genus C.hom = 9) :
    actualTrace k C c₀ 9 schurPolynomial = 15240960 := by
  have h := CurvePowerActualSchurTrace.actualSchur_trace k C c₀ hC hg9
  rw [← quotientMap_schurPolynomial k C c₀] at h
  exact h

theorem schurPolynomial_topTrace (hg9 : genus C.hom = 9) :
    topTrace k (power C 9).hom 9
      (nativeEvaluation (Stacks.Chow.fieldChowSituation k) (power C 9).hom
        (variableLine k C c₀ 9) schurPolynomial) = 15240960 :=
  (actualTrace_eq_topTrace_evaluation k C c₀ hC 9 schurPolynomial).symm.trans
    (schurPolynomial_actualTrace k C c₀ hC hg9)

theorem schurPolynomial_operator_ne_zero (hg9 : genus C.hom = 9) :
    nativeEvaluation (Stacks.Chow.fieldChowSituation k) (power C 9).hom
      (variableLine k C c₀ 9) schurPolynomial ≠ 0 := by
  intro he
  have ht := schurPolynomial_topTrace k C c₀ hC hg9
  rw [he, map_zero] at ht
  norm_num at ht

end Actual

end M9Native.CurvePowerSchurPolynomial
