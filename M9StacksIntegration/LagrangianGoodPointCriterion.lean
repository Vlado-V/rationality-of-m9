module

public import M9StacksIntegration.LagrangianExpectedGoodOpen
public import M9StacksIntegration.LagrangianLinearSectionSmooth

/-! The original universal LG family has the proved absolute source
dimension46.  Thus a genuine original smooth irreducible point curve of
dimension1 lies in the original canonical good open, with no source
regularity, source dimension, flatness, or relative-smoothness premise. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.LagrangianGoodPointCriterion

open LagrangianLinearSections
variable (K : Type u) [Field K] [CharZero K]

/-- Original actual point-curve geometry supplies an actual good
parameter of the original universal family. -/
theorem fieldPoint_lands_goodOpen
    (p : Spec (.of K) ⟶ parameter K) (hp : p ≫ parameterProjection K = 𝟙 _)
    [Smooth (pullback.snd (familyProjection K) p)]
    [IrreducibleSpace (pullback (C := Scheme.{u}) (familyProjection K) p)]
    (hF : topologicalKrullDim (pullback (C := Scheme.{u}) (familyProjection K) p) = 1) :
    ∀ t : Spec (.of K), p t ∈ ProperSmoothLocus.goodOpen (familyProjection K) := by
  let : SmoothOfRelativeDimension 46 (LagrangianExpectedGoodOpen.absoluteProjection K) :=
    LagrangianLinearSectionSmooth.absoluteProjection_smoothOfRelativeDimension K
  exact LagrangianExpectedGoodOpen.fieldPoint_lands_goodOpen K p hp hF

/-- The same actual criterion for the native parameter constructed from
the actual surjective five-equation matrix. -/
theorem matrixPoint_lands_goodOpen
    (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective (Matrix.mulVec M))
    [Smooth (pullback.snd (familyProjection K) (SplitMatrixGrassmannian.fieldPoint 9 14 K M hM))]
    [IrreducibleSpace (pullback (C := Scheme.{u}) (familyProjection K)
      (SplitMatrixGrassmannian.fieldPoint 9 14 K M hM))]
    (hF : topologicalKrullDim (pullback (C := Scheme.{u}) (familyProjection K)
      (SplitMatrixGrassmannian.fieldPoint 9 14 K M hM)) = 1) :
    ∀ t : Spec (.of K), SplitMatrixGrassmannian.fieldPoint 9 14 K M hM t ∈
      ProperSmoothLocus.goodOpen (familyProjection K) :=
  fieldPoint_lands_goodOpen K (SplitMatrixGrassmannian.fieldPoint 9 14 K M hM)
    (SplitMatrixGrassmannian.fieldPoint_projection 9 14 K M hM) hF

end M9Native.LagrangianGoodPointCriterion
