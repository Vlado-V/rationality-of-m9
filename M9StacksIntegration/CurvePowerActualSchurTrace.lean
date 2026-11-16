module

public import M9StacksIntegration.CurvePowerActualModifiedTriple
public import M9StacksIntegration.CurvePowerFiniteTopPower

/-! The literal integral Schur trace on the actual nine-fold curve-power
trace quotient. Every local point/diagonal relation is supplied by its
proved geometric theorem; no numerical relation or Schur formula is an
input. Identification with a bundle realization is a separate step. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.CurvePower

universe u
namespace M9Native.CurvePowerActualSchurTrace

open CurvePowerActualTraceRelations CurvePowerActualTraceNormalization
open CurvePowerActualModifiedTriple CurvePowerFiniteTopPower

variable (k : Type u) [Field k] [IsAlgClosed k]
  (C : Over (Spec (.of k))) [IsVariety k C.hom] [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)
  (hC : topologicalKrullDim C.left = 1)

/-- The actual quotient element built from the original coordinate point
classes and reduced diagonals, with the literal finite zero extension. -/
def actualSchur : TraceQuotient k C c₀ 9 :=
  (CurvePowerRootChern.segreSchurMatrix
    (CurvePowerRootSums.roots 9 (extendZero (point k C c₀ 9))
      (CurvePowerTopPower.boundary (extendZero₂ (reducedDiagonal k C c₀ 9))) 9)).det

include hC

/-- The actual genus-nine Chow trace of the actual Schur quotient element.
All hypotheses are properties of the original smooth proper curve. -/
theorem actualSchur_trace (hg9 : genus C.hom = 9) :
    trace k C c₀ 9 (actualSchur k C c₀) = 15240960 := by
  unfold actualSchur
  exact segreSchur_trace_nine (trace k C c₀ 9)
    (point k C c₀ 9) (reducedDiagonal k C c₀ 9)
    (point_square k C c₀ hC 9)
    (fun i j _ => point_mul_reducedDiagonal_left k C c₀ hC 9 i j)
    (fun i j _ => point_mul_reducedDiagonal_right k C c₀ hC 9 i j)
    (fun i j _ => reducedDiagonal_square_genus_nine k C c₀ hC hg9 9 i j)
    (fun i j l hij hjl => reducedDiagonal_cross_distinct k C c₀ hC 9 i j l
      (ne_of_lt hij) (ne_of_lt (lt_trans hij hjl)) (ne_of_lt hjl))
    (trace_pointProduct k C c₀ hC 9)

/-- The same trace value with the original additive polynomial trace and
its genuine trace-radical quotient map exposed literally. -/
theorem quotientTrace_actualSchur (hg9 : genus C.hom = 9) :
    CurvePowerTraceRadical.quotientTrace (CurvePowerPointTrace.actualTrace k C c₀ 9)
      (actualSchur k C c₀) = 15240960 :=
  actualSchur_trace k C c₀ hC hg9

/-- Nonvanishing follows from the actual integral degree, without any
faithfulness or nonvanishing premise on a later realization. -/
theorem actualSchur_ne_zero (hg9 : genus C.hom = 9) : actualSchur k C c₀ ≠ 0 := by
  intro he
  have ht := actualSchur_trace k C c₀ hC hg9
  rw [he, map_zero] at ht
  norm_num at ht

end M9Native.CurvePowerActualSchurTrace
