module

public import M9StacksIntegration.MukaiPrimitiveProjector
public import M9StacksIntegration.MukaiQuarticCubic

/-!
# The genuine cubic on native primitive projective forms

The action on the quotient is induced from the actual third exterior
power; no coordinate action is assumed. The canonical representative
intertwines this action with the exterior action. Consequently the actual
quartic and its actual trace-polarized cubic have the required covariance
on the native `Dual Primitive` model.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open Module Matrix

namespace M9Native.MukaiPrimitiveQuartic

open LagrangianField MukaiPrimitiveDuality MukaiConormalPrimitive MukaiPrimitiveProjector
open MukaiQuarticHitchin MukaiQuarticCubic

variable (K : Type*) [Field K] [CharZero K]

abbrev Forms := Module.Dual K (Primitive K)

def quotientMap (g : V K →ₗ[K] V K) : Forms K →ₗ[K] Forms K :=
  factor K ((primitiveClass K).comp (exteriorPower.map 3 g))

theorem quotientMap_primitiveClass (g : V K →ₗ[K] V K)
    (hσ : exteriorPower.map 2 g (sigma K) = sigma K) (w : Third K) :
    quotientMap K g (primitiveClass K w) = primitiveClass K (exteriorPower.map 3 g w) := by
  have hL (v : V K) :
      ((primitiveClass K).comp (exteriorPower.map 3 g)) (wedgeSigma K v) = 0 := by
    rw [LinearMap.comp_apply, wedgeSigma_map K g hσ, primitiveClass_wedgeSigma]
  exact (factor_restriction K ((primitiveClass K).comp (exteriorPower.map 3 g)) hL
    (coefficientDuality K w)).trans (by rw [LinearEquiv.symm_apply_apply]; rfl)

theorem representative_quotientMap (g : V K →ₗ[K] V K)
    (hω : ∀ v w, omega K (g v) (g w) = omega K v w)
    (hσ : exteriorPower.map 2 g (sigma K) = sigma K) (ell : Forms K) :
    representative K (quotientMap K g ell) = exteriorPower.map 3 g (representative K ell) := by
  obtain ⟨w, rfl⟩ := primitiveClass_surjective K ell
  rw [quotientMap_primitiveClass K g hσ, representative_primitiveClass,
    representative_primitiveClass, projector_map K g hω hσ]

theorem quotientMap_id : quotientMap K LinearMap.id = LinearMap.id := by
  apply LinearMap.ext
  intro ell
  obtain ⟨w, rfl⟩ := primitiveClass_surjective K ell
  rw [quotientMap_primitiveClass K LinearMap.id (by simp), exteriorPower.map_id]
  rfl

theorem quotientMap_comp (g h : V K →ₗ[K] V K)
    (hσg : exteriorPower.map 2 g (sigma K) = sigma K)
    (hσh : exteriorPower.map 2 h (sigma K) = sigma K) :
    quotientMap K (g.comp h) = (quotientMap K g).comp (quotientMap K h) := by
  apply LinearMap.ext
  intro ell
  obtain ⟨w, rfl⟩ := primitiveClass_surjective K ell
  have hσ : exteriorPower.map 2 (g.comp h) (sigma K) = sigma K := by
    rw [exteriorPower.map_comp, LinearMap.comp_apply, hσh, hσg]
  rw [LinearMap.comp_apply, quotientMap_primitiveClass K (g.comp h) hσ,
    quotientMap_primitiveClass K h hσh, quotientMap_primitiveClass K g hσg,
    exteriorPower.map_comp, LinearMap.comp_apply]

def primitiveQuartic (ell : Forms K) : K := quartic K (representative K ell)

def primitiveCubic : Forms K →ₗ[K] Forms K →ₗ[K] Forms K →ₗ[K] Module.Dual K (Forms K) where
  toFun u :=
    { toFun := fun v =>
        { toFun := fun w =>
            (cubic K (representative K u) (representative K v) (representative K w)).comp
              (representative K)
          map_add' := by
            intro w z
            apply LinearMap.ext
            intro t
            simp
          map_smul' := by
            intro c w
            apply LinearMap.ext
            intro t
            simp }
      map_add' := by
        intro v w
        apply LinearMap.ext
        intro z
        apply LinearMap.ext
        intro t
        simp
      map_smul' := by
        intro c v
        apply LinearMap.ext
        intro w
        apply LinearMap.ext
        intro t
        simp }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro z
    apply LinearMap.ext
    intro t
    simp
  map_smul' := by
    intro c u
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro t
    simp

theorem primitiveCubic_apply (u v w t : Forms K) :
    primitiveCubic K u v w t =
      cubic K (representative K u) (representative K v) (representative K w)
        (representative K t) := rfl

theorem primitiveQuartic_covariance (g : V K ≃ₗ[K] V K)
    (hω : ∀ v w, omega K (g v) (g w) = omega K v w)
    (hσ : exteriorPower.map 2 g.toLinearMap (sigma K) = sigma K) (ell : Forms K) :
    primitiveQuartic K (quotientMap K g.toLinearMap ell) =
      (LinearMap.det g.toLinearMap)^2 * primitiveQuartic K ell := by
  rw [primitiveQuartic, representative_quotientMap K g.toLinearMap hω hσ,
    quartic_covariance, primitiveQuartic]

theorem primitiveCubic_covariance (g : V K ≃ₗ[K] V K)
    (hω : ∀ v w, omega K (g v) (g w) = omega K v w)
    (hσ : exteriorPower.map 2 g.toLinearMap (sigma K) = sigma K) (u v w t : Forms K) :
    primitiveCubic K (quotientMap K g.toLinearMap u) (quotientMap K g.toLinearMap v)
      (quotientMap K g.toLinearMap w) (quotientMap K g.toLinearMap t) =
      (LinearMap.det g.toLinearMap)^2 * primitiveCubic K u v w t := by
  simp only [primitiveCubic_apply, representative_quotientMap K g.toLinearMap hω hσ]
  exact cubic_covariance K g _ _ _ _

end M9Native.MukaiPrimitiveQuartic
