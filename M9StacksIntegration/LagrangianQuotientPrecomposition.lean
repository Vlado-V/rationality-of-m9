module

public import M9StacksIntegration.LagrangianCotangentQuotientFrame
public import M9StacksIntegration.LagrangianFreeMatrixPullback

/-! Literal original dual coefficients under a change of ambient free coordinates. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped BigOperators

universe u

namespace M9Native.LagrangianQuotientPrecomposition

open LagrangianGrassmannian LagrangianMatrixChart LagrangianDualCoefficients
open LagrangianFreeMatrixPullback
open Stacks.AlgebraicGeometry.ReflexiveModules

variable {X : Scheme.{u}} {Q : X.Modules}

/-- The original global coefficient matrix restricted to an actual open. -/
def matrixOnOpen (a : freeOn X 6 ⟶ freeOn X 6) (U : X.Opens) :
    Matrix (Fin 6) (Fin 6) Γ(X,U) :=
  (Stacks.FreeSheafMatrix.toMatrix a).map
    (X.presheaf.map (homOfLE (show U≤⊤ from le_top)).op).hom

/-- Actual quotient basis images expand with the original free-map
coefficients, on every actual open. -/
theorem quotientVector_precomp (a : freeOn X 6 ⟶ freeOn X 6) (q : freeOn X 6 ⟶ Q)
    (U : X.Opens) (j : Fin 6) :
    quotientVector (a ≫ q) U j=
      ∑ i : Fin 6,matrixOnOpen a U i j • quotientVector q U i := by
  unfold quotientVector
  change (Q.val.restrictₛₗ (homOfLE (show U≤⊤ from le_top)).op)
    (q.app ⊤ (a.app ⊤ (freeVector X j)))=_
  rw [end_column_eq_sum]
  simp only [map_sum,Scheme.Modules.Hom.app_smul,map_smulₛₗ,
    matrixOnOpen,Matrix.map_apply]
  all_goals rfl

/-- Ambient coordinate change acts on the actual quotient-dual
coefficients by the transpose of the original restricted matrix. -/
theorem coefficientMap_precomp (a : freeOn X 6 ⟶ freeOn X 6) (q : freeOn X 6 ⟶ Q)
    (U : X.Opens) :
    coefficientMap (a ≫ q) U=
      (matrixOnOpen a U).transpose.mulVecLin.comp (coefficientMap q U) := by
  apply LinearMap.ext
  intro α
  funext j
  change evalAt Q α (quotientVector (a ≫ q) U j)=_
  rw [quotientVector_precomp]
  change dualEvalLinearMap Q α (∑ i : Fin 6,matrixOnOpen a U i j • quotientVector q U i)=_
  simp only [map_sum,map_smul,smul_eq_mul,LinearMap.comp_apply,Matrix.mulVecLin_apply,
    Matrix.mulVec,dotProduct,Matrix.transpose_apply]
  rfl

end M9Native.LagrangianQuotientPrecomposition
