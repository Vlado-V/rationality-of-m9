module

public import M9StacksIntegration.LagrangianHyperplaneCoordinates
public import M9StacksIntegration.LagrangianSymmetricPlucker

/-! The literal original coefficient rows agree with the native dual
linear forms of the quotient-plane model. The structural-map scalar
convention is compared explicitly. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections
open scoped BigOperators

universe u

namespace M9Native.LagrangianHyperplaneRows

open LagrangianGrassmannian LagrangianPluckerQuotient
open LagrangianProjectiveLinearForms LagrangianSymmetricPlucker
variable (K : Type u) [Field K]
attribute [local instance] LagrangianSymmetricPlucker.overBase globalSectionsModule

/-- The original coefficient map is the actual native structural scalar map. -/
theorem coefficientMap_eq_baseRingHom :
    LagrangianHyperplaneCoordinates.coefficientMap K = baseRingHom K (space K) := by
  simp only [LagrangianHyperplaneCoordinates.coefficientMap, LagrangianPlucker.coefficientMap,
    Category.id_comp]
  rfl

/-- The literal global-function scalar sum equals the actual native
field scalar sum, rather than silently changing module structures. -/
theorem determinantSection_eq_native_sum (v : Fin 14 → K) :
    LagrangianHyperplaneCoordinates.determinantSection K v =
      ∑ i : Fin 14, v i • primitiveSections K i := by
  apply Finset.sum_congr rfl
  intro i _
  change LagrangianHyperplaneCoordinates.coefficientMap K (v i) • primitiveSections K i =
    baseRingHom K (space K) (v i) • primitiveSections K i
  rw [coefficientMap_eq_baseRingHom]

/-- The actual original determinant section of a matrix row is the
actual native dual linear form used by the quotient-plane classifier. -/
theorem determinantSection_row (M : Matrix (Fin 5) (Fin 14) K) (j : Fin 5) :
    LagrangianHyperplaneCoordinates.determinantSection K (M j) =
      sectionLinear K (rowForms K M.mulVecLin j) := by
  rw [sectionLinear_matrix_row]
  exact determinantSection_eq_native_sum K (M j)

/-- Actual all-test vanishing of original row sections is exactly the
native quotient-plane row condition. -/
theorem pullback_row_zero_iff {T : Scheme.{u}} (f : T ⟶ space K)
    (M : Matrix (Fin 5) (Fin 14) K) (j : Fin 5) :
    pullbackGlobalSections f (determinantLine K)
        (LagrangianHyperplaneCoordinates.determinantSection K (M j)) = 0 ↔
      pullbackGlobalSections f (determinantLine K)
        (sectionLinear K (rowForms K M.mulVecLin j)) = 0 := by
  rw [determinantSection_row]

end M9Native.LagrangianHyperplaneRows
