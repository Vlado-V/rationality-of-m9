module

public import M9StacksIntegration.SymmetricSquareExteriorDuality
public import M9StacksIntegration.SymmetricSquareIntegerTensorPower

/-!
# Actual determinant normalization for the symmetric square of a dual bundle

The source is the native sixth exterior power of the native symmetric
square of the actual dual. The target is the native integer tensor
power of the original determinant line at exponent minus four.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundleDeterminant
open M9Native.SymmetricSquareBundleDeterminant
open M9Native.SymmetricSquareIntegerTensorPower

universe u

namespace M9Native.SymmetricSquareDualDeterminant

variable {X : Scheme.{u}}

/-- The actual symmetric square determinant, expressed through the actual dual determinant. -/
def dualSymmetricDeterminantPositiveIso (F : X.Modules)
    [hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 3]
    [Invertible (2 : Γ(X, ⊤))] :
    topExterior ((Scheme.Modules.symmetricAlgebra X (dualSheaf F)).piece 2) 6 ≅
      SheafOfModules.tensorPower (Opens.grothendieckTopology X) (dualSheaf (topExterior F 3)) 4 := by
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (dualSheaf F) 3 :=
    isFiniteLocallyFreeOfRank_dualSheaf F 3 hF
  exact symmetricSquareDeterminantIso (dualSheaf F) ≪≫
    positiveTensorCongr (SymmetricSquareExteriorDuality.topExteriorDualIso F) 4

/-- Actual dual/integer-power normalization, with determinant-line invertibility
proved from the original rank-three condition. No comparison is supplied as data. -/
def symmetricSquareDualDeterminantIso (F : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 3]
    [Invertible (2 : Γ(X, ⊤))] :
    letI : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (topExterior F 3) :=
      Scheme.Modules.isInvertible_exteriorPower_self F 3
    topExterior ((Scheme.Modules.symmetricAlgebra X (dualSheaf F)).piece 2) 6 ≅
      Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2
        (topExterior F 3) (-4) := by
  letI hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (topExterior F 3) :=
    Scheme.Modules.isInvertible_exteriorPower_self F 3
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (topExterior F 3) :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry X.presheaf X.ringCatSheaf.2
      (topExterior F 3) hL
  exact dualSymmetricDeterminantPositiveIso F ≪≫ positiveDualIsoNegative (topExterior F 3) 4

end M9Native.SymmetricSquareDualDeterminant
