module

public import M9StacksIntegration.OpenPullbackFunctional
public import M9StacksIntegration.LagrangianTripleDeterminantCoordinates
public import M9StacksIntegration.LagrangianRowDifferential

/-!
# Original local dual equation frames and the literal triple determinant

A genuine quotient frame determines the original local dual determinant
section. Its evaluation on the actual original primitive hyperplane is
the determinant of the actual triple matrix, read over the original
ambient open. The true original five-section row map retains this same
local equation and its native universal differential.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.LagrangianLocalTripleDeterminant

open LagrangianMatrixChart LagrangianUniversalSections LagrangianUniversalTriples
open Stacks.AlgebraicGeometry.ReflexiveModules

variable (K : Type u) [Field K] [CharZero K]
  (U : (LagrangianGrassmannian.space K).affineOpens)
  (e : bundle K (U : (LagrangianGrassmannian.space K).Opens).ι ≅
    freeOn (U : Scheme.{u}) 3)

/-- Literal triple matrix over the original ambient open. -/
def localMatrix (s : Fin 3 → (Fin 6 → K)) :
    Matrix (Fin 3) (Fin 3) Γ(LagrangianGrassmannian.space K, (U : (LagrangianGrassmannian.space K).Opens)) :=
  (Stacks.FreeSheafMatrix.toMatrix
    (evaluation K ((U : (LagrangianGrassmannian.space K).Opens).ι ≫
      LagrangianGrassmannian.projection K) (U : (LagrangianGrassmannian.space K).Opens).ι s ≫ e.hom)).map
    (Scheme.Opens.topIso (U : (LagrangianGrassmannian.space K).Opens)).hom.hom

/-- The actual original local dual section derived from the genuine quotient frame. -/
def localFunctional : Γ(dualSheaf (LagrangianPluckerQuotient.determinantLine K),
    (U : (LagrangianGrassmannian.space K).Opens)) :=
  OpenPullbackFunctional.ofPullback (LagrangianPluckerQuotient.determinantLine K)
    (U : (LagrangianGrassmannian.space K).Opens)
    (LagrangianTripleDeterminantCoordinates.framedLineIso K
      (U : (LagrangianGrassmannian.space K).Opens).ι e).hom

/-- The original local dual frame is a genuine unit functional. -/
theorem exists_local_pairing_one :
    ∃ m : Γ(LagrangianPluckerQuotient.determinantLine K,
      (U : (LagrangianGrassmannian.space K).Opens)),
      evalAt (LagrangianPluckerQuotient.determinantLine K) (localFunctional K U e) m = 1 :=
  OpenPullbackFunctional.exists_eval_ofPullback_eq_one _ _
    (LagrangianTripleDeterminantCoordinates.framedLineIso K
      (U : (LagrangianGrassmannian.space K).Opens).ι e)

/-- The actual original primitive hyperplane has exactly the original local triple determinant. -/
theorem local_hyperplane_eq_det (s : Fin 3 → (Fin 6 → K)) :
    evalAt (LagrangianPluckerQuotient.determinantLine K) (localFunctional K U e)
      ((LagrangianPluckerQuotient.determinantLine K).presheaf.map (homOfLE le_top).op
        (LagrangianHyperplaneCoordinates.determinantSection K
          (PrimitiveDecomposableNonzero.coefficients K s))) =
      (localMatrix K U e s).det := by
  refine (OpenPullbackFunctional.eval_ofPullback _ _ _ _).trans ?_
  refine (congrArg (fun z => (Scheme.Opens.topIso
    (U : (LagrangianGrassmannian.space K).Opens)).hom z)
    (LagrangianTripleDeterminantCoordinates.framedLineIso_hyperplane K _ _ rfl e s)).trans ?_
  exact ((Scheme.Opens.topIso (U : (LagrangianGrassmannian.space K).Opens)).hom.hom.map_det
    (Stacks.FreeSheafMatrix.toMatrix
      (evaluation K ((U : (LagrangianGrassmannian.space K).Opens).ι ≫
        LagrangianGrassmannian.projection K) (U : (LagrangianGrassmannian.space K).Opens).ι s ≫
          e.hom)))

variable (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)

/-- A genuine original coefficient relation gives exactly the local determinant equation. -/
theorem row_local_equation (a : Fin 5 → K) (s : Fin 3 → (Fin 6 → K))
    (h : PrimitiveDecomposableNonzero.coefficients K s = Matrix.vecMul a M) :
    evalAt (LagrangianPluckerQuotient.determinantLine K) (localFunctional K U e)
      ((LagrangianPluckerQuotient.determinantLine K).presheaf.map (homOfLE le_top).op
        ((LagrangianRowDifferential.rowProjection K a).app ⊤
          (LagrangianFibreFiveSection.fiveSection K M hM))) =
      (localMatrix K U e s).det := by
  rw [LagrangianFixedEquationRows.rowProjection_fiveSection, ← h]
  exact local_hyperplane_eq_det K U e s

/-- The same original actual row conormal map is the differential of that literal local determinant. -/
theorem rowDifferential_adjunction_matrix
    [SmoothOfRelativeDimension 1 (LagrangianFiveSectionModel.structureMap K
      (LagrangianFibreFiveSection.fiveSection K M hM))]
    (a : Fin 5 → K) (s : Fin 3 → (Fin 6 → K))
    (h : PrimitiveDecomposableNonzero.coefficients K s = Matrix.vecMul a M) :
    (((Scheme.Modules.pullbackPushforwardAdjunction
        (LagrangianFiveSectionModel.inclusion K
          (LagrangianFibreFiveSection.fiveSection K M hM))).homEquiv _ _
        (LagrangianRowDifferential.rowDifferential K
          (LagrangianFibreFiveSection.fiveSection K M hM) a)).val.app
      (op (U : (LagrangianGrassmannian.space K).Opens))) (localFunctional K U e) =
      (((Scheme.Modules.pullbackPushforwardAdjunction
        (LagrangianFiveSectionModel.inclusion K
          (LagrangianFibreFiveSection.fiveSection K M hM))).unit.app
          (Scheme.Hom.relativeDifferentials (LagrangianGrassmannian.projection K))).val.app
        (op (U : (LagrangianGrassmannian.space K).Opens))).hom
        ((Scheme.Hom.universalRelativeDerivation (LagrangianGrassmannian.projection K)).d
          (localMatrix K U e s).det) := by
  rw [LagrangianRowDifferential.rowDifferential_adjunction_apply,
    row_local_equation K U e M hM a s h]

end M9Native.LagrangianLocalTripleDeterminant
