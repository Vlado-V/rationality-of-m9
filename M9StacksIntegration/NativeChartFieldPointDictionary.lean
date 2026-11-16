module

public import M9StacksIntegration.NativeStackCoverageDenseImage
public import M9StacksIntegration.SmoothStackIntegralAtlas

/-! Actual chart scheme points and actual classifier field objects.
The native represented-chart homeomorphism supplies the dictionary; the
ground-field representative is constructed from its original scheme map
and exact structural triangle. No representative/refinement premise occurs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

open AlgebraicGeometry CategoryTheory
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
attribute [local instance] Stack.reprPointTopology

namespace M9Native.NativeChartFieldPointDictionary
open NativeStackCoverageDenseImage

universe u w
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A genuine original field-valued point computes the actual chart
point as its actual native classifier object. -/
theorem schemePointMap_fieldPoint
    {X : Stack.AlgebraicStacks.{u, w} B S hS} {U : BigFppfOver B S hS}
    (a : Stack.schemeStack B S hS U ⟶ X)
    (p : Space.FieldValuedPoint B S hS (schemeSpace U).obj) :
    SmoothStackIntegralAtlas.schemePointMap B S hS a (Space.schemePoint B S hS U p) =
      Stack.pointClass B S hS X.val.val X.val.isFiberedInGroupoids
        (classifierFieldPoint B S hS a.hom.hom p) := by
  let z := Stack.representedChartPointMap B S hS U (p.class B S hS (schemeSpace U).obj)
  have hz : Stack.pointsHomeomorphScheme B S hS U z = Space.schemePoint B S hS U p := by
    rw [Stack.pointsHomeomorphScheme_representedChartPointMap]
    exact Space.pointsToScheme_class B S hS U p
  have he : (Stack.pointsHomeomorphScheme B S hS U).symm (Space.schemePoint B S hS U p) = z := by
    apply (Stack.pointsHomeomorphScheme B S hS U).injective
    rw [Homeomorph.apply_symm_apply, hz]
  change Stack.pointsMap B S hS (Stack.schemeFibredCategory B S hS U).val
    _ X.val.isFiberedInGroupoids a.hom.hom
      ((Stack.pointsHomeomorphScheme B S hS U).symm _) = _
  rw [he]
  change Stack.pointsMap B S hS _ _ _ a.hom.hom
    (Stack.spacePointMap B S hS (schemeSpace U).obj (Stack.schemeFibredCategory B S hS U)
      (Stack.representingEquivalence B S hS (schemeSpace U).obj
        (Stack.schemeFibredCategory B S hS U) (Stack.representedChart B S hS U)).functor
      (p.class B S hS (schemeSpace U).obj)) = _
  rw [Stack.spacePointMap_class, Stack.pointsMap_class]
  rfl

variable {K : Type u} [Field K] (hK : B.Contains (Spec (.of K)))
  {U : BigFppfOver B (Spec (.of K)) hK}

/-- The actual ground-field representative, with the canonical
Spec.map(id) structural arrow and the original chart morphism as value. -/
def groundFieldPoint
    (b : Spec (.of K) ⟶ (BigFppfOver.toScheme B (Spec (.of K)) hK).obj U)
    (hb : b ≫ B.inclusion.map U.hom = 𝟙 _) :
    Space.FieldValuedPoint B (Spec (.of K)) hK (schemeSpace U).obj where
  carrier := K
  contained := hK
  toBase := Spec.map (CommRingCat.ofHom (RingHom.id K))
  value := Over.homMk (B.inclusion.preimage b) (by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, B.inclusion.map_preimage]
    change b ≫ B.inclusion.map U.hom = Spec.map (CommRingCat.ofHom (RingHom.id K))
    simpa only [CommRingCat.ofHom_id, Spec.map_id] using hb)

/-- The constructed native site's map is the literal original b. -/
theorem groundFieldPoint_value
    (b : Spec (.of K) ⟶ (BigFppfOver.toScheme B (Spec (.of K)) hK).obj U)
    (hb : b ≫ B.inclusion.map U.hom = 𝟙 _) :
    (BigFppfOver.toScheme B (Spec (.of K)) hK).map
      (groundFieldPoint B hK b hb).value = b := by
  change B.inclusion.map (B.inclusion.preimage b : B.obj hK ⟶ U.left) = b
  exact B.inclusion.map_preimage (X := B.obj hK) (Y := U.left) b

/-- The exact dictionary required by actual ground-field chart density.
Its right-hand field point has base siteObject(...,Spec.map(id)). -/
theorem schemePointMap_groundFieldPoint
    {X : Stack.AlgebraicStacks.{u, w} B (Spec (.of K)) hK}
    (b : Spec (.of K) ⟶ (BigFppfOver.toScheme B (Spec (.of K)) hK).obj U)
    (hb : b ≫ B.inclusion.map U.hom = 𝟙 _)
    (a : Stack.schemeStack B (Spec (.of K)) hK U ⟶ X) :
    SmoothStackIntegralAtlas.schemePointMap B (Spec (.of K)) hK a
        (b (IsLocalRing.closedPoint K)) =
      Stack.pointClass B (Spec (.of K)) hK X.val.val X.val.isFiberedInGroupoids
        (classifierFieldPoint B (Spec (.of K)) hK a.hom.hom (groundFieldPoint B hK b hb)) := by
  have h := schemePointMap_fieldPoint B (Spec (.of K)) hK a (groundFieldPoint B hK b hb)
  change SmoothStackIntegralAtlas.schemePointMap B (Spec (.of K)) hK a
    ((BigFppfOver.toScheme B (Spec (.of K)) hK).map
      (groundFieldPoint B hK b hb).value (IsLocalRing.closedPoint K)) = _ at h
  rw [groundFieldPoint_value] at h
  exact h

end M9Native.NativeChartFieldPointDictionary
