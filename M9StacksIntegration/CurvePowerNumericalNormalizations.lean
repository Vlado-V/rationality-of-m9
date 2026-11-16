module

public import M9StacksIntegration.CurvePowerGammaVanishing
public import M9StacksIntegration.CurvePowerSelfClassDegree

/-!
# Actual genus normalization of the numerical diagonal rules

The coefficient is evaluated using the actual smooth-curve cotangent
degree. The original seven-term combination itself has no loop
coefficient, so its proved vanishing is independent of the displayed
formal self parameter.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
open Stacks.CurvePower

universe u

namespace M9Native.CurvePowerNumericalNormalizations

open CurvePowerDiagonalSelfRestriction CurvePowerGammaPoint
open CurvePowerGraphInduction CurvePowerGraphContexts

variable (k : Type u) [Field k] [IsAlgClosed k]
  (C : Over (Spec (.of k))) [IsVariety k C.hom] [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (hC : topologicalKrullDim C.left = 1)

include hC

theorem selfDegree_genus : selfDegree k C hC = 2 - 2 * (genus C.hom : ℤ) := by
  let : IsCurve k C.hom := (isCurve_iff k C.hom).mpr ⟨inferInstance,hC⟩
  exact CurvePowerSelfClassDegree.selfClass1_degree_genus k C
    (CurvePowerPointWordDegree.power_one_dim k C hC).le

theorem selfDegree_genus_nine (hg : genus C.hom = 9) : selfDegree k C hC = -16 := by
  rw [selfDegree_genus k C hC, hg]
  norm_num

theorem gammaValue_eq_zero_any_parameter (c₀ : power C 0 ⟶ C) (t : ℤ) (ambient : ℕ)
    (frame : AdmissibleFrame) (word : List (CurvePowerChowFunctional.Letter ambient)) :
    gammaValue t (actualFunctional k C c₀ ambient) frame word = 0 := by
  simpa only [gammaValue, realization_embed] using
    CurvePowerGammaVanishing.gammaValue_eq_zero k C c₀ hC ambient frame word

end M9Native.CurvePowerNumericalNormalizations
