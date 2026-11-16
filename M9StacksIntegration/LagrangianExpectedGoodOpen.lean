module

public import M9StacksIntegration.RationalSectionGoodOpen
public import M9StacksIntegration.LagrangianLinearSections
public import M9StacksIntegration.SplitMatrixGrassmannian
public import StacksFrontier.AlgebraicGeometry.GrassmannianScheme.Smooth

/-! The expected smooth-fibre criterion on the original native universal
five-section family.  The parameter dimension is proved from the original
native Grassmannian.  The absolute source-dimension instance is the exact
literal map constructed by the independent total-incidence geometry. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.LagrangianExpectedGoodOpen

open LagrangianLinearSections

variable (K : Type u) [Field K]

/-- The original absolute structure morphism, with the literal universal
family projection retained. -/
abbrev absoluteProjection : family K ⟶ Spec (.of K) :=
  familyProjection K ≫ parameterProjection K

instance parameter_smoothOfRelativeDimension :
    SmoothOfRelativeDimension 45 (parameterProjection K) := by
  change SmoothOfRelativeDimension (9 * (14-9))
    (AlgebraicGeometry.Grassmannian.schemeOver.over 9 14 (Spec (.of K))).hom
  infer_instance

instance parameter_smooth : Smooth (parameterProjection K) :=
  SmoothOfRelativeDimension.smooth 45 (parameterProjection K)

instance parameter_isLocallyNoetherian : IsLocallyNoetherian (parameter K) :=
  LocallyOfFiniteType.isLocallyNoetherian (parameterProjection K)

instance familyProjection_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (familyProjection K) := by infer_instance

/-- A genuine smooth irreducible original point fibre of dimension one
belongs to the actual canonical good open.  The arithmetic is the proved
parameter dimension45 and the actual source dimension46. -/
theorem fieldPoint_lands_goodOpen
    [SmoothOfRelativeDimension 46 (absoluteProjection K)]
    (p : Spec (.of K) ⟶ parameter K) (hp : p ≫ parameterProjection K = 𝟙 _)
    [Smooth (pullback.snd (familyProjection K) p)]
    [IrreducibleSpace (pullback (C := Scheme.{u}) (familyProjection K) p)]
    (hF : topologicalKrullDim (pullback (C := Scheme.{u}) (familyProjection K) p) =
      (1 : WithBot ℕ∞)) :
    ∀ t : Spec (.of K), p t ∈ ProperSmoothLocus.goodOpen (familyProjection K) :=
  RationalSectionGoodOpen.section_lands_goodOpen_of_smooth_pullback
    (n := 46) (m := 45) (r := 1) (absoluteProjection K) (parameterProjection K)
      (familyProjection K) p hp hF rfl

/-- In particular the original surjective five-equation matrix gives an
actual good parameter once its actual pullback is the constructed smooth
irreducible curve.  No good-open or relative-smoothness premise is assumed. -/
theorem matrixPoint_lands_goodOpen
    [SmoothOfRelativeDimension 46 (absoluteProjection K)]
    (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective (Matrix.mulVec M))
    [Smooth (pullback.snd (familyProjection K) (SplitMatrixGrassmannian.fieldPoint 9 14 K M hM))]
    [IrreducibleSpace (pullback (C := Scheme.{u}) (familyProjection K)
      (SplitMatrixGrassmannian.fieldPoint 9 14 K M hM))]
    (hF : topologicalKrullDim (pullback (C := Scheme.{u}) (familyProjection K)
      (SplitMatrixGrassmannian.fieldPoint 9 14 K M hM)) = (1 : WithBot ℕ∞)) :
    ∀ t : Spec (.of K), SplitMatrixGrassmannian.fieldPoint 9 14 K M hM t ∈
      ProperSmoothLocus.goodOpen (familyProjection K) :=
  fieldPoint_lands_goodOpen K (SplitMatrixGrassmannian.fieldPoint 9 14 K M hM)
    (SplitMatrixGrassmannian.fieldPoint_projection 9 14 K M hM) hF

end M9Native.LagrangianExpectedGoodOpen
