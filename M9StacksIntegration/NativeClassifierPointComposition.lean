module

public import M9StacksIntegration.NativeStackCoverageDenseImage

/-! The actual classifier map on native field-valued points.
Yoneda evaluation derives the image object in the genuine category of
elements, and the native common-refinement relation derives point equality.
No equality of a chosen coarse model or supplied compatibility is used.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.PresheafOfCategories
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.NativeClassifierPointComposition
open NativeStackCoverageDenseImage

universe u w
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Stack.AlgebraicStacks.{u, w} B S hS} {M : AlgebraicSpaces B S hS}

/-- On any actual field point, Yoneda evaluation gives the literal
postcomposed native classifier object. -/
theorem classifier_image_object
    (f : X ⟶ Stack.algebraicSpaceStack.{u, w} B S hS M.obj M.property)
    {U : BigFppfOver B S hS}
    (A : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ X.val.val)
    (p : Space.FieldValuedPoint B S hS (schemeSpace U).obj) :
    f.hom.hom.obj (classifierFieldPoint B S hS A p).obj =
      (Stack.spaceFieldValuedPoint B S hS M.obj
        (Space.FieldValuedPoint.map B S hS (schemeSpace U).obj
          (ASClassifierGeometricLift.nativeMap B S hS f A).hom p)).obj := by
  let F := BasedFunctor.comp (ASClassifierGeometricLift.classifier B S hS A)
    (ASClassifierGeometricLift.coarseFunctor B S hS f)
  refine obj_eq_of_elementOf_eq (Functor.congr_obj F.w (Over.mk p.value)) rfl ?_
  exact (PresheafValuedClassifierReflection.representingMap_app F p.siteObject p.value).symm

/-- The point map of the actual algebraic-space classifier equals the
actual source-stack point map followed by the real AS/stack comparison. -/
theorem coarsePointMap_classifierFieldPoint
    (f : X ⟶ Stack.algebraicSpaceStack.{u, w} B S hS M.obj M.property)
    {U : BigFppfOver B S hS}
    (A : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ X.val.val)
    (p : Space.FieldValuedPoint B S hS (schemeSpace U).obj) :
    coarsePointMap B S hS f
        (Stack.pointClass B S hS X.val.val X.val.isFiberedInGroupoids
          (classifierFieldPoint B S hS A p)) =
      Space.pointsMap B S hS (schemeSpace U).obj
        (ASClassifierGeometricLift.nativeMap B S hS f A).hom
        (p.class B S hS (schemeSpace U).obj) := by
  let := Space.pointTopology B S hS M.obj
  let := Stack.pointTopology B S hS
    (Stack.algebraicSpaceStack.{u, w} B S hS M.obj M.property).val
  apply (NativeStackSpacePointTopology.pointsHomeomorphSpace.{u, w}
    B S hS M.obj M.property).injective
  rw [coarsePointMap, Function.comp_apply, Homeomorph.apply_symm_apply]
  change Stack.pointsMap B S hS X.val.val X.val.isFiberedInGroupoids
    _ f.hom.hom _ = Stack.spacePointMap B S hS M.obj (Stack.fibredCategory B S hS M.obj)
      (BasedFunctor.id (Stack.fibredCategory B S hS M.obj).val) _
  rw [Stack.pointsMap_class, Space.pointsMap_class, Stack.spacePointMap_class]
  apply (Stack.class_eq_class_iff_hasCommonExtension B S hS _ _ _ _).2
  refine ⟨Stack.fieldValuedPointMap B S hS X.val.val f.hom.hom
    (classifierFieldPoint B S hS A p), ⟨𝟙 _⟩, ⟨?_⟩⟩
  exact eqToHom (classifier_image_object B S hS f A p)

/-- An actual source arrow to any chosen representative establishes
coverage by the literal algebraic-space classifier point map. -/
theorem coarsePoint_mem_range_of_arrow
    (f : X ⟶ Stack.algebraicSpaceStack.{u, w} B S hS M.obj M.property)
    {U : BigFppfOver B S hS}
    (A : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ X.val.val)
    (p : Space.FieldValuedPoint B S hS (schemeSpace U).obj)
    (q : Stack.FieldValuedPoint B S hS X.val.val)
    (a : (classifierFieldPoint B S hS A p).obj ⟶ q.obj) :
    coarsePointMap B S hS f
        (Stack.pointClass B S hS X.val.val X.val.isFiberedInGroupoids q) ∈
      Set.range (Space.pointsMap B S hS (schemeSpace U).obj
        (ASClassifierGeometricLift.nativeMap B S hS f A).hom) := by
  refine ⟨p.class B S hS (schemeSpace U).obj, ?_⟩
  rw [← coarsePointMap_classifierFieldPoint B S hS f A p,
    pointClass_eq_of_arrow B S hS (classifierFieldPoint B S hS A p) q a]

end M9Native.NativeClassifierPointComposition
