module

public import StacksFrontier.AlgebraicGeometry.CurveDegreeDeterminant
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic

/-!
# The actual rank-two determinant line

The native second exterior power has rank one and is therefore
invertible. No curve, degree, or cohomology hypothesis is required.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.MukaiTwistBounds

variable {X : Scheme.{u}}

/-- The second exterior power is the genuine invertible determinant line. -/
theorem exterior_two_isInvertible (F : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2] :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (Scheme.Modules.exteriorPower F 2) := by
  letI := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self F 2
  exact Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace _

end M9Native.MukaiTwistBounds
