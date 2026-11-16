module

public import M9StacksIntegration.MukaiRankTwoExterior
public import StacksFrontier.AlgebraicGeometry.CurveDegreeDeterminantModification

/-!
# Native degree of the actual rank-two determinant

The top exterior degree theorem is applied to the original bundle;
the determinant degree is not assigned as additional data.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.MukaiTwistBounds

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f]

/-- The original rank-two degree equals that of its actual determinant. -/
theorem degree_exterior_two (F : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2] :
    letI := exterior_two_isInvertible F
    invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le
      (Scheme.Modules.exteriorPower F 2) =
        curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le F 2 := by
  letI := exterior_two_isInvertible F
  letI := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self F 2
  rw [invertibleCurveDegree_eq_curveDegree]
  exact (curveDegree_eq_curveDegree_exteriorPower_of_isCurve k f
    (IsCurve.topologicalKrullDim_eq_one f).le 1 F).symm

end M9Native.MukaiTwistBounds
