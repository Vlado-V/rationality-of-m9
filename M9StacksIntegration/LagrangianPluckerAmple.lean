module

public import M9StacksIntegration.LagrangianPluckerGeneration
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample

/-!
# Actual ampleness of the LG universal determinant

The actual primitive Plucker closed immersion pulls back the actual
ample projective hyperplane sheaf. The checked original-section O(1)
comparison transports this to the actual universal quotient determinant.
The final theorem uses the literal native ampleness predicate consumed
by the numerical degree API, with no ampleness hypothesis.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.LagrangianDegree

open M9Native.LagrangianGrassmannian M9Native.LagrangianPluckerQuotient

variable (K : Type u) [Field K] [CharZero K]

/-- Ampleness in the section-power spelling of the actual native theory. -/
theorem determinantLine_isAmple :
    Stacks.Ample.IsAmple (space K) (determinantLine K) := by
  let L := Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf 13 (base K)
  let f := M9Native.LagrangianPlucker.primitivePlucker K
  letI : Stacks.Ample.IsInvertibleModule (space K)
      ((Scheme.Modules.pullback f).obj L) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback f L
  have hL : Stacks.Ample.IsAmple (AlgebraicGeometry.ProjectiveSpace 13 (base K)) L :=
    Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf 13 (base K)
  have hp : Stacks.Ample.IsAmple (space K) ((Scheme.Modules.pullback f).obj L) :=
    Stacks.AmplePullback.isAmple_modulePullback_of_isClosedImmersion f L hL
  exact (Stacks.RelativeVeryAmple.isAmple_congr _ _
    (M9Native.LagrangianPluckerGeneration.determinantLineO1Iso K)).mp hp

/-- The original determinant is ample in the exact predicate used by
native intersection numbers and degreeWithRespectTo. -/
theorem determinantLine_modulesIsAmple :
    Scheme.Modules.IsAmple (space K) (determinantLine K) :=
  Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple
    (space K) (determinantLine K) (determinantLine_isAmple K)

end M9Native.LagrangianDegree
