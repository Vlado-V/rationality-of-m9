module

public import M9StacksIntegration.FiveCartierCutsDegree
public import M9StacksIntegration.SmoothIntegralHyperplaneCuts
public import M9StacksIntegration.LagrangianPluckerAmple

/-!
# The genuine five-cut curve retains the actual LG ample degree

All five divisors and their original determinant-line identifications
are the actual Bertini prefix construction. Native Cartier restriction
and the native curve Euler comparison give the equality below, with no
degree-sixteen, genus, cycle-class or chosen-flag premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u
namespace M9Native.LagrangianFiveCutDegree
open AlgebraicGeometry CategoryTheory
open M9Native.SmoothIntegralHyperplaneCuts
open Stacks.Divisors

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]

instance projection_isProper : IsProper (LagrangianGrassmannian.projection K) :=
  isProper_of_isProjectiveMorphism _
    (LagrangianPluckerClosed.isProjectiveMorphism_projection K)

instance fiveCutToLG_isClosedImmersion : IsClosedImmersion (fiveCutToLG K) :=
  (fifthState K).closed

/-- The actual determinant restriction on the actual smooth integral
five-cut curve has the original LG's actual sixfold ample degree. -/
theorem fiveCut_curveDegree :
    invertibleCurveDegree K (fiveCutToLG K ≫ LagrangianGrassmannian.projection K)
        (fiveCutCurve_dimension K).le
        ((Scheme.Modules.pullback (fiveCutToLG K)).obj
          (LagrangianPluckerQuotient.determinantLine K)) =
      degreeWithRespectTo K (LagrangianGrassmannian.projection K)
        (𝟙 (LagrangianGrassmannian.space K)) 6 (LagrangianIntegral.space_dimension K)
        (LagrangianPluckerQuotient.determinantLine K)
        (LagrangianDegree.determinantLine_modulesIsAmple K) := by
  let D₁ := nextDivisor (initialSystem K) (initialSystem_generates K)
    (initialSystem_immersive K) (initialState K)
  let D₂ := nextDivisor (initialSystem K) (initialSystem_generates K)
    (initialSystem_immersive K) (firstState K)
  let D₃ := nextDivisor (initialSystem K) (initialSystem_generates K)
    (initialSystem_immersive K) (secondState K)
  let D₄ := nextDivisor (initialSystem K) (initialSystem_generates K)
    (initialSystem_immersive K) (thirdState K)
  let D₅ := nextDivisor (initialSystem K) (initialSystem_generates K)
    (initialSystem_immersive K) (fourthState K)
  have hD₁ : IsEffectiveCartierDivisor D₁ := nextDivisor_cartier (initialSystem K)
    (initialSystem_generates K) (initialSystem_immersive K) (initialState K)
  have hD₂ : IsEffectiveCartierDivisor D₂ := nextDivisor_cartier (initialSystem K)
    (initialSystem_generates K) (initialSystem_immersive K) (firstState K)
  have hD₃ : IsEffectiveCartierDivisor D₃ := nextDivisor_cartier (initialSystem K)
    (initialSystem_generates K) (initialSystem_immersive K) (secondState K)
  have hD₄ : IsEffectiveCartierDivisor D₄ := nextDivisor_cartier (initialSystem K)
    (initialSystem_generates K) (initialSystem_immersive K) (thirdState K)
  have hD₅ : IsEffectiveCartierDivisor D₅ := nextDivisor_cartier (initialSystem K)
    (initialSystem_generates K) (initialSystem_immersive K) (fourthState K)
  obtain ⟨hd, h⟩ := @FiveCartierCutsDegree.degree_after_five_cartier_cuts K _
    (LagrangianGrassmannian.space K) (LagrangianGrassmannian.projection K) _
    (LagrangianIntegral.space_dimension K) (LagrangianPluckerQuotient.determinantLine K) _
    (LagrangianDegree.determinantLine_modulesIsAmple K)
    D₁ hD₁ D₂ hD₂ D₃ hD₃ D₄ hD₄ D₅ hD₅
    (nextOriginalDivisorLineIso K (initialState K))
    (nextOriginalDivisorLineIso K (firstState K))
    (nextOriginalDivisorLineIso K (secondState K))
    (nextOriginalDivisorLineIso K (thirdState K))
    (nextOriginalDivisorLineIso K (fourthState K))
  exact h

end M9Native.LagrangianFiveCutDegree
