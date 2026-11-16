module

public import M9StacksIntegration.CurvePowerActualTraceRelations
public import M9StacksIntegration.CurvePowerNumericalNormalizations

/-! The actual genus-nine trace quotient and its normalized point and
reduced-diagonal rules. The trace is the original integral Chow degree. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Stacks.CurvePower

universe u
namespace M9Native.CurvePowerActualTraceNormalization

open CurvePowerChowFunctional CurvePowerPointTrace CurvePowerActualTraceRelations
open CurvePowerTraceRadical CurvePowerNumericalNormalizations

variable (k : Type u) [Field k] [IsAlgClosed k]
  (C : Over (Spec (.of k))) [IsVariety k C.hom] [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)
  (hC : topologicalKrullDim C.left = 1)

def trace (n : ℕ) : TraceQuotient k C c₀ n →+ ℤ :=
  quotientTrace (actualTrace k C c₀ n)

theorem trace_mk (n : ℕ) (p : MvPolynomial (Letter n) ℤ) :
    trace k C c₀ n
      (Ideal.Quotient.mk (PolynomialTraceRelations.radical (actualWordDegree k C c₀ n)) p) =
      actualTrace k C c₀ n p := rfl

include hC

theorem trace_pointProduct (n : ℕ) :
    trace k C c₀ n (∏ i : Fin n, point k C c₀ n i) = 1 := by
  change quotientTrace (actualTrace k C c₀ n)
    (∏ i : Fin n, Ideal.Quotient.mk (traceRadical (actualTrace k C c₀ n))
      (MvPolynomial.X (Sum.inl i : Letter n))) = 1
  rw [← map_prod]
  exact actualTrace_pointProduct k C c₀ hC n

theorem point_mul_reducedDiagonal_left (n : ℕ) (i j : Fin n) :
    point k C c₀ n i * reducedDiagonal k C c₀ n i j = 0 :=
  CurvePowerDiagonalAlgebra.point_mul_reducedDiagonal_left _ _ _
    (point_square k C c₀ hC n i) (point_diagonal k C c₀ hC n i j)

theorem point_mul_reducedDiagonal_right (n : ℕ) (i j : Fin n) :
    point k C c₀ n j * reducedDiagonal k C c₀ n i j = 0 :=
  CurvePowerDiagonalAlgebra.point_mul_reducedDiagonal_right _ _ _
    (point_square k C c₀ hC n j) (point_diagonal_right k C c₀ hC n i j)

theorem reducedDiagonal_square_genus_nine (hg : genus C.hom = 9)
    (n : ℕ) (i j : Fin n) :
    reducedDiagonal k C c₀ n i j ^ 2 =
      -18 * point k C c₀ n i * point k C c₀ n j := by
  have h := reducedDiagonal_square k C c₀ hC n i j
  rw [selfDegree_genus_nine k C hC hg] at h
  norm_num at h
  simpa only [neg_mul] using h

theorem diagonal_self_genus_nine (hg : genus C.hom = 9) (n : ℕ) (i : Fin n) :
    diagonal k C c₀ n i i = -16 * point k C c₀ n i := by
  have h := diagonal_self k C c₀ hC n i
  rw [selfDegree_genus_nine k C hC hg] at h
  norm_num at h
  simpa only [neg_mul] using h

end M9Native.CurvePowerActualTraceNormalization
