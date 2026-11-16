module

public import M9StacksIntegration.MukaiCastelnuovoLinear
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.Determinant

/-!
# Canonical exterior operations for the genuine quartic construction

All maps act on actual exterior powers. The interior product is obtained
from its universal alternating formula, and its naturality is proved on
actual decomposable generators. The volume is the actual determinant
form, so its covariance is the native determinant-composition theorem.

The intended quartic is the canonical construction in Hitchin,
"The geometry of three-forms in six and seven dimensions", §2.1,
https://arxiv.org/pdf/math/0010054 . No invariant or determinant
restriction formula is assumed here.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open Module Matrix

namespace M9Native.MukaiQuarticExterior

variable (K : Type*) [Field K]
variable {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

def wedgeMul (m n : ℕ) : (⋀[K]^m V) →ₗ[K] (⋀[K]^n V) →ₗ[K] (⋀[K]^(m+n) V) where
  toFun u :=
    { toFun := fun v => ⟨u.val * v.val, SetLike.mul_mem_graded u.property v.property⟩
      map_add' := by intro v w; apply Subtype.ext; exact mul_add _ _ _
      map_smul' := by intro c v; apply Subtype.ext; exact mul_smul_comm c u.val v.val }
  map_add' := by
    intro u w
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact add_mul _ _ _
  map_smul' := by
    intro c u
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact smul_mul_assoc c u.val v.val

theorem wedgeMul_map (m n : ℕ) (f : V →ₗ[K] W) (u : ⋀[K]^m V) (v : ⋀[K]^n V) :
    exteriorPower.map (m+n) f (wedgeMul K m n u v) =
      wedgeMul K m n (exteriorPower.map m f u) (exteriorPower.map n f v) := by
  apply Subtype.ext
  simp [wedgeMul, exteriorPower.coe_map]

def wedge2 : V →ₗ[K] V →ₗ[K] (⋀[K]^2 V) :=
  MukaiCastelnuovoLinear.asBilinear (exteriorPower.ιMulti K 2)

theorem wedge2_self (v : V) : wedge2 K v v = 0 :=
  MukaiCastelnuovoLinear.alternating_pair_diag (exteriorPower.ιMulti K 2) v

theorem wedge2_swap (u v : V) : wedge2 K u v = -wedge2 K v u :=
  MukaiCastelnuovoLinear.alternating_pair_swap (exteriorPower.ιMulti K 2) u v

theorem wedge2_map (f : V →ₗ[K] W) (u v : V) :
    exteriorPower.map 2 f (wedge2 K u v) = wedge2 K (f u) (f v) := by
  change exteriorPower.map 2 f (exteriorPower.ιMulti K 2 ![u,v]) =
    exteriorPower.ιMulti K 2 ![f u,f v]
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  ext i
  fin_cases i <;> rfl

def interiorAlternating (φ : Module.Dual K V) : V [⋀^Fin 3]→ₗ[K] (⋀[K]^2 V) where
  toFun v := φ (v 0) • wedge2 K (v 1) (v 2) -
    φ (v 1) • wedge2 K (v 0) (v 2) + φ (v 2) • wedge2 K (v 0) (v 1)
  map_update_add' := by
    intro d v i a b
    have hd : d = instDecidableEqFin 3 := Subsingleton.elim _ _
    cases hd
    fin_cases i <;> simp [Function.update, add_smul, smul_add] <;> module
  map_update_smul' := by
    intro d v i c a
    have hd : d = instDecidableEqFin 3 := Subsingleton.elim _ _
    cases hd
    fin_cases i <;> simp [Function.update, smul_smul, smul_add, smul_sub] <;> module
  map_eq_zero_of_eq' := by
    intro v i j hij hne
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · change v 0 = v 1 at hij
      simp [hij,wedge2_self]
    · change v 0 = v 2 at hij
      rw [hij,wedge2_swap K (v 1) (v 2)]
      simp [wedge2_self,smul_neg]
    · change v 1 = v 0 at hij
      simp [hij,wedge2_self]
    · exact (hne rfl).elim
    · change v 1 = v 2 at hij
      simp [hij,wedge2_self]
    · change v 2 = v 0 at hij
      rw [hij,wedge2_swap K (v 1) (v 0)]
      simp [wedge2_self,smul_neg]
    · change v 2 = v 1 at hij
      simp [hij,wedge2_self]
    · exact (hne rfl).elim

def interior (φ : Module.Dual K V) : (⋀[K]^3 V) →ₗ[K] (⋀[K]^2 V) :=
  exteriorPower.alternatingMapLinearEquiv (interiorAlternating K φ)

theorem interior_ιMulti (φ : Module.Dual K V) (v : Fin 3 → V) :
    interior K φ (exteriorPower.ιMulti K 3 v) =
      φ (v 0) • wedge2 K (v 1) (v 2) -
      φ (v 1) • wedge2 K (v 0) (v 2) + φ (v 2) • wedge2 K (v 0) (v 1) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

theorem interior_add_functional (φ ψ : Module.Dual K V) :
    interior K (φ+ψ) = interior K φ + interior K ψ := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.add_apply, interior_ιMulti, add_smul]
  module

theorem interior_smul_functional (c : K) (φ : Module.Dual K V) :
    interior K (c • φ) = c • interior K φ := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.smul_apply, interior_ιMulti,
    smul_eq_mul, mul_smul, smul_sub, smul_add]

theorem interior_map (f : V →ₗ[K] W) (φ : Module.Dual K W) (w : ⋀[K]^3 V) :
    interior K φ (exteriorPower.map 3 f w) =
      exteriorPower.map 2 f (interior K (φ.comp f) w) := by
  have h : (interior K φ).comp (exteriorPower.map 3 f) =
      (exteriorPower.map 2 f).comp (interior K (φ.comp f)) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, interior_ιMulti, map_sub, map_add, map_smul, wedge2_map]
    rfl
  exact LinearMap.congr_fun h w

def volume : (⋀[K]^6 (Fin 6 → K)) →ₗ[K] K :=
  exteriorPower.alternatingMapLinearEquiv (Pi.basisFun K (Fin 6)).det

theorem volume_ιMulti (v : Fin 6 → (Fin 6 → K)) :
    volume K (exteriorPower.ιMulti K 6 v) = (Pi.basisFun K (Fin 6)).det v :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

theorem volume_map (f : (Fin 6 → K) →ₗ[K] (Fin 6 → K)) (w : ⋀[K]^6 (Fin 6 → K)) :
    volume K (exteriorPower.map 6 f w) = LinearMap.det f * volume K w := by
  have h : (volume K).comp (exteriorPower.map 6 f) = LinearMap.det f • volume K := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, volume_ιMulti, Module.Basis.det_comp,
      LinearMap.smul_apply, smul_eq_mul]
  exact LinearMap.congr_fun h w

end M9Native.MukaiQuarticExterior
