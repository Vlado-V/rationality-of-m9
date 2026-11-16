module

public import M9StacksIntegration.LagrangianPluckerAmple
public import M9StacksIntegration.LagrangianPluckerClosed
public import M9StacksIntegration.LagrangianFundamentalClasses
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ChowDegree

/-!
# The actual Plucker degree as an actual sixfold first-Chern cap degree

The line is the original universal quotient determinant. Its proved
isomorphism with the actual primitive Plucker pullback O(1), and its
proved ampleness, fix the geometric meaning of this native degree.
This file establishes the comparison with actual Chow operations;
it does not assume or assert the still-missing numerical value16.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory
open Stacks.Chow

universe u

namespace M9Native.LagrangianActualDegree

open M9Native.LagrangianGrassmannian M9Native.LagrangianPluckerQuotient
open M9Native.LagrangianDegree

variable (K : Type u) [Field K] [CharZero K]

/-- Properness is derived from the actual primitive Plucker closed immersion. -/
instance projection_isProper : IsProper (projection K) :=
  isProper_of_isProjectiveMorphism _
    (M9Native.LagrangianPluckerClosed.isProjectiveMorphism_projection K)

/-- The native numerical degree in the actual ample Plucker determinant. -/
def pluckerDegree : ℤ :=
  degreeWithRespectTo K (projection K) (𝟙 (space K)) 6
    (M9Native.LagrangianIntegral.space_dimension K) (determinantLine K)
    (determinantLine_modulesIsAmple K)

/-- Degree of the actual sixfold c1-cap on the original fundamental class. -/
def pluckerCapDegree : ℤ :=
  chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
    (projection K) (IsLocalRing.closedPoint K)
    (iteratedFirstChernCap K (projection K) (fun _ : Fin 6 => determinantLine K)
      (lagrangianOwnFundamental K))

/-- Every geometric premise of the native degree comparison is derived
from the original LG and original actual Plucker determinant. -/
theorem pluckerDegree_eq_capDegree : pluckerDegree K = pluckerCapDegree K :=
  degreeWithRespectTo_eq_chowDegree_iteratedFirstChernCap K (projection K)
    (𝟙 (space K)) 6 (M9Native.LagrangianIntegral.space_dimension K)
    (determinantLine K) (determinantLine_modulesIsAmple K)

end M9Native.LagrangianActualDegree
