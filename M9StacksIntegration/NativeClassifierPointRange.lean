module

public import M9StacksIntegration.NativeClassifierPointComposition

/-! Actual point-range membership from an actual classifier map factor.
The witness is the genuine point map of the constructed parameter arrow;
no choice or equality of field-point records is required.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

open AlgebraicGeometry CategoryTheory
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.NativeClassifierPointRange
open NativeStackCoverageDenseImage

universe u w
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Stack.AlgebraicStacks.{u,w} B S hS} {M : AlgebraicSpaces B S hS}

/-- A proved factorization of actual classifier maps places the actual
source field object's coarse point in the target classifier's range. -/
theorem mem_range_of_nativeMap_factorization
    (f : X ⟶ Stack.algebraicSpaceStack.{u,w} B S hS M.obj M.property)
    {T U : BigFppfOver B S hS}
    (A : BasedCategory.ofFunctor (Over.forget T) ⥤ᵇ X.val.val)
    (C : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ X.val.val)
    (a : T ⟶ U)
    (h : ASClassifierGeometricLift.nativeMap B S hS f A =
      schemeSpaceMap a ≫ ASClassifierGeometricLift.nativeMap B S hS f C)
    (p : Space.FieldValuedPoint B S hS (schemeSpace T).obj) :
    coarsePointMap B S hS f
        (Stack.pointClass B S hS X.val.val X.val.isFiberedInGroupoids
          (classifierFieldPoint B S hS A p)) ∈
      Set.range (Space.pointsMap B S hS (schemeSpace U).obj
        (ASClassifierGeometricLift.nativeMap B S hS f C).hom) := by
  refine ⟨Space.pointsMap B S hS (schemeSpace T).obj (schemeSpaceMap a).hom
    (p.class B S hS (schemeSpace T).obj), ?_⟩
  calc
    Space.pointsMap B S hS _ (ASClassifierGeometricLift.nativeMap B S hS f C).hom
        (Space.pointsMap B S hS _ (schemeSpaceMap a).hom (p.class B S hS _)) =
      Space.pointsMap B S hS _
        (schemeSpaceMap a ≫ ASClassifierGeometricLift.nativeMap B S hS f C).hom
          (p.class B S hS _) :=
      (congrFun (Space.pointsMap_comp B S hS _ (schemeSpaceMap a).hom
        (ASClassifierGeometricLift.nativeMap B S hS f C).hom) (p.class B S hS _)).symm
    _ = Space.pointsMap B S hS _ (ASClassifierGeometricLift.nativeMap B S hS f A).hom
        (p.class B S hS _) :=
      congrArg (fun m : schemeSpace T ⟶ M =>
        Space.pointsMap B S hS _ m.hom (p.class B S hS _)) h.symm
    _ = _ := (NativeClassifierPointComposition.coarsePointMap_classifierFieldPoint
      B S hS f A p).symm

end M9Native.NativeClassifierPointRange
