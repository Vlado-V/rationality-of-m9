module

public import M9StacksIntegration.MukaiQuarticHitchin

/-!
# Actual polarization of the exterior quartic

The maps below are formed from the same interior product, wedge product,
and determinant volume as the genuine Hitchin operator. In particular the
cubic is a trilinear map with values in actual linear functionals. Its
covariance is proved before any primitive-coordinate restriction.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open Module

namespace M9Native.MukaiQuarticCubic

open MukaiQuarticExterior MukaiQuarticHitchin

variable (K : Type*) [Field K]

def mixedTop (u v : Three K) (φ : DualSix K) (x : Six K) : ⋀[K]^6 (Six K) :=
  wedgeMul K 3 3 (wedgeMul K 1 2 (one K x) (interior K φ u)) v

def mixedOperator : Three K →ₗ[K] Three K →ₗ[K] Module.End K (DualSix K) where
  toFun u :=
    { toFun := fun v =>
        { toFun := fun φ =>
            { toFun := fun x => volume K (mixedTop K u v φ x)
              map_add' := by intro x y; simp [mixedTop]
              map_smul' := by intro c x; simp [mixedTop] }
          map_add' := by
            intro φ ψ
            apply LinearMap.ext
            intro x
            simp [mixedTop, interior_add_functional]
          map_smul' := by
            intro c φ
            apply LinearMap.ext
            intro x
            simp [mixedTop, interior_smul_functional] }
      map_add' := by
        intro v w
        apply LinearMap.ext
        intro φ
        apply LinearMap.ext
        intro x
        simp [mixedTop]
      map_smul' := by
        intro c v
        apply LinearMap.ext
        intro φ
        apply LinearMap.ext
        intro x
        simp [mixedTop] }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    simp [mixedTop]
  map_smul' := by
    intro c u
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro φ
    apply LinearMap.ext
    intro x
    simp [mixedTop]

theorem mixedOperator_apply (u v : Three K) (φ : DualSix K) (x : Six K) :
    mixedOperator K u v φ x = volume K (mixedTop K u v φ x) := rfl

theorem mixedOperator_diagonal (u : Three K) :
    mixedOperator K u u = hitchinOperator K u := rfl

theorem mixedOperator_map_evaluate (f : Six K →ₗ[K] Six K) (u v : Three K)
    (φ : DualSix K) (x : Six K) :
    mixedOperator K (exteriorPower.map 3 f u) (exteriorPower.map 3 f v) φ (f x) =
      LinearMap.det f * mixedOperator K u v (φ.comp f) x := by
  simp only [mixedOperator_apply, mixedTop]
  rw [interior_map, ← one_map K f x,
    ← wedgeMul_map K 1 2 f, ← wedgeMul_map K 3 3 f, volume_map]

theorem mixedOperator_covariance (g : Six K ≃ₗ[K] Six K) (u v : Three K) :
    mixedOperator K (exteriorPower.map 3 g.toLinearMap u) (exteriorPower.map 3 g.toLinearMap v) =
      LinearMap.det g.toLinearMap • g.dualMap.symm.conj (mixedOperator K u v) := by
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  change mixedOperator K (exteriorPower.map 3 g.toLinearMap u)
      (exteriorPower.map 3 g.toLinearMap v) φ x =
    LinearMap.det g.toLinearMap * mixedOperator K u v (φ.comp g.toLinearMap) (g.symm x)
  have h := mixedOperator_map_evaluate K g.toLinearMap u v φ (g.symm x)
  change mixedOperator K (exteriorPower.map 3 g.toLinearMap u)
      (exteriorPower.map 3 g.toLinearMap v) φ (g (g.symm x)) = _ at h
  rw [g.apply_symm_apply] at h
  exact h

def polarOperator : Three K →ₗ[K] Three K →ₗ[K] Module.End K (DualSix K) :=
  mixedOperator K + (mixedOperator K).flip

theorem polarOperator_apply (u v : Three K) :
    polarOperator K u v = mixedOperator K u v + mixedOperator K v u := rfl

theorem polarOperator_diagonal (u : Three K) :
    polarOperator K u u = (2 : K) • hitchinOperator K u := by
  rw [polarOperator_apply, mixedOperator_diagonal]
  module

theorem polarOperator_covariance (g : Six K ≃ₗ[K] Six K) (u v : Three K) :
    polarOperator K (exteriorPower.map 3 g.toLinearMap u) (exteriorPower.map 3 g.toLinearMap v) =
      LinearMap.det g.toLinearMap • g.dualMap.symm.conj (polarOperator K u v) := by
  simp only [polarOperator_apply, mixedOperator_covariance, map_add, smul_add]

/-- Actual four-linear trace polarization, curried as a cubic with values
in the actual dual of the third exterior power. -/
def cubic : Three K →ₗ[K] Three K →ₗ[K] Three K →ₗ[K] Module.Dual K (Three K) where
  toFun u :=
    { toFun := fun v =>
        { toFun := fun w =>
            { toFun := fun t => (6 : K)⁻¹ * LinearMap.trace K (DualSix K)
                (polarOperator K u v * polarOperator K w t)
              map_add' := by intro s t; simp [mul_add]
              map_smul' := by intro c t; simp [mul_left_comm] }
          map_add' := by
            intro w z
            apply LinearMap.ext
            intro t
            simp [mul_add]
          map_smul' := by
            intro c w
            apply LinearMap.ext
            intro t
            simp [mul_left_comm] }
      map_add' := by
        intro v w
        apply LinearMap.ext
        intro z
        apply LinearMap.ext
        intro t
        simp [add_mul, mul_add]
      map_smul' := by
        intro c v
        apply LinearMap.ext
        intro w
        apply LinearMap.ext
        intro t
        simp [mul_left_comm] }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro z
    apply LinearMap.ext
    intro t
    simp [add_mul, mul_add]
  map_smul' := by
    intro c u
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    apply LinearMap.ext
    intro t
    simp [mul_left_comm]

theorem cubic_apply (u v w t : Three K) :
    cubic K u v w t = (6 : K)⁻¹ * LinearMap.trace K (DualSix K)
      (polarOperator K u v * polarOperator K w t) := rfl

theorem cubic_covariance (g : Six K ≃ₗ[K] Six K) (u v w t : Three K) :
    cubic K (exteriorPower.map 3 g.toLinearMap u) (exteriorPower.map 3 g.toLinearMap v)
      (exteriorPower.map 3 g.toLinearMap w) (exteriorPower.map 3 g.toLinearMap t) =
      (LinearMap.det g.toLinearMap)^2 * cubic K u v w t := by
  simp only [cubic_apply, polarOperator_covariance]
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  change (6 : K)⁻¹ * LinearMap.trace K (DualSix K)
    ((LinearMap.det g.toLinearMap * LinearMap.det g.toLinearMap) •
      (g.dualMap.symm.conj (polarOperator K u v)).comp
        (g.dualMap.symm.conj (polarOperator K w t))) = _
  rw [← LinearEquiv.conj_comp, map_smul, LinearMap.trace_conj']
  simp only [smul_eq_mul]
  let z := LinearMap.trace K (DualSix K) (polarOperator K u v * polarOperator K w t)
  change (6 : K)⁻¹ * ((LinearMap.det g.toLinearMap * LinearMap.det g.toLinearMap) * z) =
    (LinearMap.det g.toLinearMap)^2 * ((6 : K)⁻¹ * z)
  ring

end M9Native.MukaiQuarticCubic
