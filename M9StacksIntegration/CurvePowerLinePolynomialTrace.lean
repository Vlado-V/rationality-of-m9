module

public import M9StacksIntegration.LinePolynomialEvaluation
public import M9StacksIntegration.GradedCapTopTrace

/-!
# The actual polynomial trace equals the actual top operational trace

The equality is proved monomial by monomial using actual line-family
cap words and the actual grading of the integral fundamental class.
On a curve power the required dimension is proved by the native power
dimension theorem. No realization-compatibility equality is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory MvPolynomial

universe u v

namespace M9Native.CurvePowerLinePolynomialTrace

open Stacks.Chow ChowCapWords CurveTopChowClass CurvePowerChowFunctional
open LinePolynomialEvaluation GradedCapTopTrace

section Generic

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  {α : Type v}

def evaluationTrace (N : ℕ) (L : α → InvertibleLine X) : MvPolynomial α ℤ →+ ℤ :=
  (topTrace k f N).comp (nativeEvaluation (fieldChowSituation k) f L).toAddMonoidHom

theorem evaluationTrace_eq_wordTrace [IsIntegral X] (N : ℕ)
    (hN : relativeDimension (fieldChowSituation k).dimensionFunction f (genericPoint X) = N)
    (L : α → InvertibleLine X) :
    evaluationTrace k f N L =
      CurvePowerPolynomialTrace.trace (fun w => wordDegree k f (w.map L)) := by
  apply AddMonoidHom.ext
  intro P
  induction P using MvPolynomial.induction_on' with
  | monomial e c =>
      change topTrace k f N (nativeEvaluation (fieldChowSituation k) f L (monomial e c)) =
        CurvePowerPolynomialTrace.trace (fun w => wordDegree k f (w.map L)) (monomial e c)
      rw [nativeEvaluation_monomial, map_zsmul, topTrace_familyWord k f N hN,
        CurvePowerPolynomialTrace.trace_monomial]
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ]

end Generic

section Power

open Stacks.CurvePower CurvePowerPointTrace

variable (k : Type u) [Field k] (C : Over (Spec (.of k))) [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)

def variableLine (ambient : ℕ) : Letter ambient → InvertibleLine (power C ambient).left :=
  fun i => chosenLine (letterClass k C c₀ ambient i)

variable [IsAlgClosed k] [IsVariety k C.hom] (hC : topologicalKrullDim C.left = 1)

include hC

theorem actualEvaluationTrace_eq_actualTrace (ambient : ℕ) :
    evaluationTrace k (power C ambient).hom ambient (variableLine k C c₀ ambient) =
      actualTrace k C c₀ ambient := by
  have hIntegral : IsIntegral (power C ambient).left := (isVariety_power C ambient).toIsIntegral
  have hdim : topologicalKrullDim (power C ambient).left = (ambient : WithBot ℕ∞) := by
    rw [(isVariety_power_and_topologicalKrullDim C ambient).2, hC, mul_one]
  have hN := relativeDimension_fieldChowSituation_genericPoint (power C ambient).hom hdim
  have h := evaluationTrace_eq_wordTrace k (power C ambient).hom ambient hN
    (variableLine k C c₀ ambient)
  have hf : (fun w : List (Letter ambient) => wordDegree k (power C ambient).hom
      (w.map (variableLine k C c₀ ambient))) = actualWordDegree k C c₀ ambient := by
    funext w
    have hL : w.map (variableLine k C c₀ ambient) =
        (w.map (letterClass k C c₀ ambient)).map chosenLine := by
      rw [List.map_map]
      apply List.map_congr_left
      intro i _
      rfl
    exact congrArg (wordDegree k (power C ambient).hom) hL
  rw [hf] at h
  exact h

theorem actualTrace_eq_topTrace_evaluation (ambient : ℕ)
    (P : MvPolynomial (Letter ambient) ℤ) :
    actualTrace k C c₀ ambient P =
      topTrace k (power C ambient).hom ambient
        (nativeEvaluation (fieldChowSituation k) (power C ambient).hom
          (variableLine k C c₀ ambient) P) := by
  have h := congrArg (fun A : MvPolynomial (Letter ambient) ℤ →+ ℤ => A P)
    (actualEvaluationTrace_eq_actualTrace k C c₀ hC ambient)
  exact h.symm

end Power

end M9Native.CurvePowerLinePolynomialTrace
