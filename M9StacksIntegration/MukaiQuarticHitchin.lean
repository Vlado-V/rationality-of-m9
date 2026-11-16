module

public import M9StacksIntegration.MukaiQuarticExterior
public import Mathlib.LinearAlgebra.Trace

/-!
# The actual Hitchin operator and relative quartic invariant

The operator is made from the proved universal interior product, actual
graded exterior multiplication and the actual determinant volume. Its
covariance follows from those maps' naturality. Taking the trace of its
square gives the genuine relative invariant, with determinant weight two.

Reference: N. Hitchin, "The geometry of three-forms in six and seven
dimensions", §2.1, Definition 1 and equation (1),
https://arxiv.org/pdf/math/0010054 .
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open Module

namespace M9Native.MukaiQuarticHitchin

open MukaiQuarticExterior

variable (K : Type*) [Field K]

abbrev Six := Fin 6 → K
abbrev Three := ⋀[K]^3 (Six K)
abbrev DualSix := Module.Dual K (Six K)

def one : Six K →ₗ[K] (⋀[K]^1 (Six K)) :=
  (exteriorPower.oneEquiv K (Six K)).symm.toLinearMap

theorem one_ιMulti (u : Six K) :
    one K u = exteriorPower.ιMulti K 1 (fun _ => u) := by
  apply (exteriorPower.oneEquiv K (Six K)).injective
  simp [one]

theorem one_map (f : Six K →ₗ[K] Six K) (u : Six K) :
    exteriorPower.map 1 f (one K u) = one K (f u) := by
  rw [one_ιMulti, one_ιMulti, exteriorPower.map_apply_ιMulti]
  rfl

def topExpression (w : Three K) (φ : DualSix K) (u : Six K) : ⋀[K]^6 (Six K) :=
  wedgeMul K 3 3 (wedgeMul K 1 2 (one K u) (interior K φ w)) w

def hitchinOperator (w : Three K) : Module.End K (DualSix K) where
  toFun φ :=
    { toFun := fun u => volume K (topExpression K w φ u)
      map_add' := by intro u v; simp [topExpression]
      map_smul' := by intro c u; simp [topExpression] }
  map_add' := by
    intro φ ψ
    ext u
    simp [topExpression, interior_add_functional, LinearMap.add_apply]
  map_smul' := by
    intro c φ
    ext u
    simp [topExpression, interior_smul_functional]

theorem hitchinOperator_apply (w : Three K) (φ : DualSix K) (u : Six K) :
    hitchinOperator K w φ u = volume K (topExpression K w φ u) := rfl

/-- Canonical covariance before choosing an inverse or coordinates. -/
theorem hitchinOperator_map_evaluate (f : Six K →ₗ[K] Six K) (w : Three K)
    (φ : DualSix K) (u : Six K) :
    hitchinOperator K (exteriorPower.map 3 f w) φ (f u) =
      LinearMap.det f * hitchinOperator K w (φ.comp f) u := by
  simp only [hitchinOperator_apply, topExpression]
  rw [interior_map, ← one_map K f u,
    ← wedgeMul_map K 1 2 f, ← wedgeMul_map K 3 3 f, volume_map]

theorem hitchinOperator_covariance (g : Six K ≃ₗ[K] Six K) (w : Three K) :
    hitchinOperator K (exteriorPower.map 3 g.toLinearMap w) =
      LinearMap.det g.toLinearMap • g.dualMap.symm.conj (hitchinOperator K w) := by
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro u
  change hitchinOperator K (exteriorPower.map 3 g.toLinearMap w) φ u =
    LinearMap.det g.toLinearMap * hitchinOperator K w (φ.comp g.toLinearMap) (g.symm u)
  have h := hitchinOperator_map_evaluate K g.toLinearMap w φ (g.symm u)
  change hitchinOperator K (exteriorPower.map 3 g.toLinearMap w) φ (g (g.symm u)) = _ at h
  rw [g.apply_symm_apply] at h
  exact h

/-- The genuine exterior-algebra quartic, with the literal coefficient
1/6 in Hitchin's definition. -/
def quartic (w : Three K) : K :=
  (6 : K)⁻¹ * LinearMap.trace K (DualSix K) (hitchinOperator K w * hitchinOperator K w)

/-- The determinant weight is DERIVED from the actual wedge operator
and trace-conjugation identity; it is not an invariant hypothesis. -/
theorem quartic_covariance (g : Six K ≃ₗ[K] Six K) (w : Three K) :
    quartic K (exteriorPower.map 3 g.toLinearMap w) =
      (LinearMap.det g.toLinearMap)^2 * quartic K w := by
  let d := LinearMap.det g.toLinearMap
  let e := g.dualMap.symm
  have hm : (d • e.conj (hitchinOperator K w)) * (d • e.conj (hitchinOperator K w)) =
      d^2 • e.conj (hitchinOperator K w * hitchinOperator K w) := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, pow_two]
    change (d * d) • (e.conj (hitchinOperator K w)).comp (e.conj (hitchinOperator K w)) =
      (d * d) • e.conj ((hitchinOperator K w).comp (hitchinOperator K w))
    rw [e.conj_comp]
  simp only [quartic, hitchinOperator_covariance]
  change (6 : K)⁻¹ * LinearMap.trace K (DualSix K)
    ((d • e.conj (hitchinOperator K w)) * (d • e.conj (hitchinOperator K w))) = _
  rw [hm, map_smul, LinearMap.trace_conj']
  simp only [smul_eq_mul]
  ring

end M9Native.MukaiQuarticHitchin
