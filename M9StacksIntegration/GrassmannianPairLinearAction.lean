module

public import M9StacksIntegration.GrassmannianLinearAction
public import M9StacksIntegration.GrassmannianProductCharts

/-! The actual independent constant linear action on the genuine native
product of two four-plane Grassmannians, and its generic-stalk pullback. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix

universe u

namespace M9Native.GrassmannianPairLinearAction

variable (K : Type u) [Field K]

abbrev GL6 := GrassmannianLinearAction.GL6 K
abbrev space := GrassmannianProductCharts.productSpace K 4 6
abbrev projection := GrassmannianProductCharts.productProjection K 4 6

def action (g h : GL6 K) : space K ⟶ space K :=
  pullback.lift (pullback.fst _ _ ≫ GrassmannianLinearAction.action K g)
    (pullback.snd _ _ ≫ GrassmannianLinearAction.action K h) (by
      simp only [Category.assoc, GrassmannianLinearAction.action_projection]
      exact pullback.condition)

@[reassoc] theorem action_fst (g h : GL6 K) :
    action K g h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ GrassmannianLinearAction.action K g :=
  pullback.lift_fst _ _ _

@[reassoc] theorem action_snd (g h : GL6 K) :
    action K g h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ GrassmannianLinearAction.action K h :=
  pullback.lift_snd _ _ _

@[reassoc] theorem action_projection (g h : GL6 K) : action K g h ≫ projection K = projection K := by
  change action K g h ≫ (pullback.fst _ _ ≫ GrassmannianLinearAction.projection K) = _
  rw [← Category.assoc, action_fst, Category.assoc, GrassmannianLinearAction.action_projection]
  rfl

theorem action_one : action K 1 1 = 𝟙 (space K) := by
  apply pullback.hom_ext
  · rw [action_fst, GrassmannianLinearAction.action_one, Category.comp_id, Category.id_comp]
  · rw [action_snd, GrassmannianLinearAction.action_one, Category.comp_id, Category.id_comp]

theorem action_mul (g₁ g₂ h₁ h₂ : GL6 K) :
    action K g₁ h₁ ≫ action K g₂ h₂ = action K (g₁ * g₂) (h₁ * h₂) := by
  apply pullback.hom_ext
  · rw [Category.assoc, action_fst, ← Category.assoc, action_fst,
      Category.assoc, GrassmannianLinearAction.action_mul, action_fst]
  · rw [Category.assoc, action_snd, ← Category.assoc, action_snd,
      Category.assoc, GrassmannianLinearAction.action_mul, action_snd]

def schemeAutomorphism (g h : GL6 K) : space K ≅ space K where
  hom := action K g h
  inv := action K g⁻¹ h⁻¹
  hom_inv_id := by rw [action_mul, mul_inv_cancel, mul_inv_cancel, action_one]
  inv_hom_id := by rw [action_mul, inv_mul_cancel, inv_mul_cancel, action_one]

instance action_isIso (g h : GL6 K) : IsIso (action K g h) :=
  (schemeAutomorphism K g h).isIso_hom

instance action_isDominant (g h : GL6 K) : IsDominant (action K g h) :=
  ⟨(action K g h).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

def fieldAutomorphism (g h : GL6 K) : (space K).functionField ≃ₐ[K] (space K).functionField := by
  let e := GrassmannianCharts.openImmersionFunctionFieldIso (action K g h)
  refine { __ := e.commRingCatIsoToRingEquiv, commutes' := fun c => ?_ }
  have he := GrassmannianCharts.openImmersionFunctionFieldIso_scalar K (action K g h) (projection K)
  rw [action_projection] at he
  exact DFunLike.congr_fun he c

theorem fieldAutomorphism_eq_map (g h : GL6 K) :
    (fieldAutomorphism K g h).toRingHom = NativeDominantFunctionField.map (action K g h) := by
  change (GrassmannianCharts.openImmersionFunctionFieldIso (action K g h)).hom.hom = _
  simp only [GrassmannianCharts.openImmersionFunctionFieldIso, NativeDominantFunctionField.map,
    Iso.trans_hom, asIso_hom]

theorem fieldAutomorphism_one : fieldAutomorphism K 1 1 = 1 := by
  apply AlgEquiv.ext
  intro x
  change (fieldAutomorphism K 1 1).toRingHom x = x
  rw [fieldAutomorphism_eq_map, GrassmannianLinearAction.dominantMap_congr (action_one K),
    NativeFunctionFieldFunctor.map_id]
  rfl

theorem fieldAutomorphism_mul (g₁ g₂ h₁ h₂ : GL6 K) :
    fieldAutomorphism K (g₁ * g₂) (h₁ * h₂) =
      fieldAutomorphism K g₁ h₁ * fieldAutomorphism K g₂ h₂ := by
  apply AlgEquiv.ext
  intro x
  change (fieldAutomorphism K (g₁ * g₂) (h₁ * h₂)).toRingHom x =
    (fieldAutomorphism K g₁ h₁).toRingHom ((fieldAutomorphism K g₂ h₂).toRingHom x)
  rw [fieldAutomorphism_eq_map, fieldAutomorphism_eq_map, fieldAutomorphism_eq_map,
    GrassmannianLinearAction.dominantMap_congr (action_mul K g₁ g₂ h₁ h₂).symm,
    NativeFunctionFieldFunctor.map_comp]
  rfl

def fieldRepresentation : (GL6 K × GL6 K) →*
    ((space K).functionField ≃ₐ[K] (space K).functionField) where
  toFun g := fieldAutomorphism K g.1 g.2
  map_one' := fieldAutomorphism_one K
  map_mul' g h := fieldAutomorphism_mul K g.1 h.1 g.2 h.2

end M9Native.GrassmannianPairLinearAction
