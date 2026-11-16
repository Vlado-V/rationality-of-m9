module

public import M9StacksIntegration.PrimitiveGrassmannianAction
public import M9StacksIntegration.NativeGenericPullbackEvaluation

@[expose] public section

/-! Actual constant symplectic transformations and their function-field action.

Every scheme automorphism below is obtained from the frozen native group
scheme action. Pullback is contravariant, so the homomorphism defining the
left field action uses the inverse constant scheme transformation.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace M9Native.PrimitiveConstantFieldAction

open PrimitiveGrassmannianAction PrimitiveFamilyFreeAction

abbrev Sp6 := M9.PrimitiveStabilizer.Sp6 ℂ

/-- Constant points commute with the actual morphism of test schemes. -/
theorem constantPointOn_natural {T T' : Over base} (p : T' ⟶ T) (h : Sp6) :
    p ≫ constantPointOn T h = constantPointOn T' h := by
  apply Over.OverMorphism.ext
  change p.left ≫ (T.hom ≫ _) = T'.hom ≫ _
  rw [← Category.assoc, p.w]

theorem constantPointOn_one (T : Over base) : constantPointOn T (1 : Sp6) = 1 := by
  apply (Sp6GroupScheme.pointsMulEquiv base T).injective
  simp only [pointsMulEquiv_constantPointOn, map_one]

theorem constantPointOn_mul (T : Over base) (g h : Sp6) :
    constantPointOn T (g*h) = constantPointOn T g * constantPointOn T h := by
  apply (Sp6GroupScheme.pointsMulEquiv base T).injective
  simp only [pointsMulEquiv_constantPointOn, map_mul]

/-- The literal frozen native action by a constant original Sp6 element. -/
def overMap (h : Sp6) : overSpace ⟶ overSpace :=
  lift (constantPointOn overSpace h) (𝟙 overSpace) ≫ nativeAction.act

/-- Its action on every test point is the original native action. -/
theorem overMap_comp {T : Over base} (p : T ⟶ overSpace) (h : Sp6) :
    p ≫ overMap h = lift (constantPointOn T h) p ≫ nativeAction.act := by
  change p ≫ (lift (constantPointOn overSpace h) (𝟙 overSpace) ≫ nativeAction.act) = _
  rw [nativeAction.comp_smul, constantPointOn_natural, Category.comp_id]

theorem overMap_one : overMap (1 : Sp6) = 𝟙 overSpace := by
  rw [overMap, constantPointOn_one]
  exact nativeAction.one_smul overSpace (𝟙 overSpace)

/-- Composition has the order dictated by the actual left action. -/
theorem overMap_mul (g h : Sp6) : overMap g ≫ overMap h = overMap (h*g) := by
  rw [overMap_comp]
  symm
  simpa only [overMap, constantPointOn_mul] using
    nativeAction.mul_smul overSpace (constantPointOn overSpace h)
      (constantPointOn overSpace g) (𝟙 overSpace)

def schemeMap (h : Sp6) : space ⟶ space := (overMap h).left

@[reassoc]
theorem schemeMap_projection (h : Sp6) : schemeMap h ≫ projection = projection :=
  (overMap h).w

theorem schemeMap_one : schemeMap (1 : Sp6) = 𝟙 space :=
  congrArg (fun p : overSpace ⟶ overSpace => p.left) overMap_one

theorem schemeMap_mul (g h : Sp6) : schemeMap g ≫ schemeMap h = schemeMap (h*g) :=
  congrArg (fun p : overSpace ⟶ overSpace => p.left) (overMap_mul g h)

/-- The actual scheme automorphism, with inverse provided by the group law. -/
def schemeIso (h : Sp6) : space ≅ space where
  hom := schemeMap h
  inv := schemeMap h⁻¹
  hom_inv_id := by rw [schemeMap_mul, inv_mul_cancel, schemeMap_one]
  inv_hom_id := by rw [schemeMap_mul, mul_inv_cancel, schemeMap_one]

instance schemeMap_isIso (h : Sp6) : IsIso (schemeMap h) := (schemeIso h).isIso_hom

instance schemeMap_isDominant (h : Sp6) : IsDominant (schemeMap h) :=
  ⟨(schemeMap h).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

/-- Binding to the actual old primitive matrix action on quotient classes. -/
theorem schemeMap_pointClass (T : Over base) (p : T ⟶ overSpace) (h : Sp6) :
    pointClass (p.left ≫ schemeMap h) =
      transformPoints T
        (Sp6GroupScheme.mapMatrix (scalarMap T) (PrimitiveRingFieldBridge.fromOriginal h))
        (pointClass p.left) := by
  change pointClass ((p ≫ overMap h).left) = _
  rw [overMap_comp]
  exact constant_action_pointClass T h p

/-- Actual pullback on the original native Grassmannian function field. -/
def fieldPullback (h : Sp6) : space.functionField ≃ₐ[ℂ] space.functionField := by
  let e := GrassmannianCharts.openImmersionFunctionFieldIso (schemeMap h)
  refine { __ := e.commRingCatIsoToRingEquiv, commutes' := fun c => ?_ }
  have he := GrassmannianCharts.openImmersionFunctionFieldIso_scalar ℂ (schemeMap h) projection
  rw [schemeMap_projection] at he
  exact DFunLike.congr_fun he c

theorem fieldPullback_eq_map (h : Sp6) :
    (fieldPullback h).toRingHom = NativeDominantFunctionField.map (schemeMap h) := by
  change (GrassmannianCharts.openImmersionFunctionFieldIso (schemeMap h)).hom.hom = _
  simp only [GrassmannianCharts.openImmersionFunctionFieldIso, NativeDominantFunctionField.map,
    Iso.trans_hom, asIso_hom]

private theorem dominantMap_congr {f g : space ⟶ space} [IsDominant f] [IsDominant g]
    (h : f = g) : NativeDominantFunctionField.map f = NativeDominantFunctionField.map g := by
  subst g
  rfl

theorem fieldPullback_one : fieldPullback (1 : Sp6) = 1 := by
  apply AlgEquiv.ext
  intro f
  change (fieldPullback (1 : Sp6)).toRingHom f = f
  rw [fieldPullback_eq_map, dominantMap_congr schemeMap_one, NativeFunctionFieldFunctor.map_id]
  rfl

theorem fieldPullback_mul (g h : Sp6) :
    fieldPullback (g*h) = fieldPullback h * fieldPullback g := by
  apply AlgEquiv.ext
  intro f
  change (fieldPullback (g*h)).toRingHom f =
    (fieldPullback h).toRingHom ((fieldPullback g).toRingHom f)
  rw [fieldPullback_eq_map, fieldPullback_eq_map, fieldPullback_eq_map,
    dominantMap_congr (schemeMap_mul h g).symm, NativeFunctionFieldFunctor.map_comp]
  rfl

/-- The actual left field action is pullback along inverse scheme translation. -/
def fieldAction : Sp6 →* (space.functionField ≃ₐ[ℂ] space.functionField) where
  toFun h := fieldPullback h⁻¹
  map_one' := by simpa using fieldPullback_one
  map_mul' g h := by rw [mul_inv_rev, fieldPullback_mul]

@[simp]
theorem fieldAction_apply (h : Sp6) : fieldAction h = fieldPullback h⁻¹ := rfl

/-- Invariance under all actual field-action elements is exactly invariance
under all actual constant scheme pullbacks. -/
theorem fixed_iff_pullback_fixed (f : space.functionField) :
    (∀ h : Sp6, fieldAction h f = f) ↔ (∀ h : Sp6, fieldPullback h f = f) := by
  constructor
  · intro hf h
    simpa using hf h⁻¹
  · intro hf h
    exact hf h⁻¹

end M9Native.PrimitiveConstantFieldAction
