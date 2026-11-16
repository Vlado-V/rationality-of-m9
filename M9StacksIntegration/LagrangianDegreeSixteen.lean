module

public import M9StacksIntegration.LagrangianFlagDegreeComparison

/-!
# The degree of the original Lagrangian Grassmannian is sixteen

The original ample determinant degree is reduced to its actual top-Chern
ambient numerator, normalized on the original quotient flag, transported
along the native flag isomorphism and integrated by the proved actual
free-six projective-bundle pushes.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory Stacks.Chow
universe u
namespace M9Native.LagrangianActualDegree
open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianDegree

variable (K : Type u) [Field K] [CharZero K]

/-- The original sixfold determinant-cap zero cycle has degree sixteen. -/
theorem pluckerCapDegree_eq_sixteen : pluckerCapDegree K = 16 :=
  (pluckerCapDegree_eq_ambientNumerator K).trans
    ((LagrangianFlagDegreeComparison.ambient_degree_eq_nativeA K).trans
      ((LagrangianFlagDegreeComparison.nativeA_degree_eq_nativeB K).trans
        (LagrangianFlagDegreeComparison.nativeB_degree_eq_sixteen K)))

/-- The actual original Plucker ample degree is sixteen. -/
theorem pluckerDegree_eq_sixteen : pluckerDegree K = 16 :=
  (pluckerDegree_eq_capDegree K).trans (pluckerCapDegree_eq_sixteen K)

/-- The original native ample-degree expression, with all geometric hypotheses derived. -/
theorem degreeWithRespectTo_determinant_eq_sixteen :
    degreeWithRespectTo K (projection K) (𝟙 (space K)) 6
      (LagrangianIntegral.space_dimension K) (determinantLine K)
      (LagrangianDegree.determinantLine_modulesIsAmple K) = 16 :=
  pluckerDegree_eq_sixteen K

end M9Native.LagrangianActualDegree
