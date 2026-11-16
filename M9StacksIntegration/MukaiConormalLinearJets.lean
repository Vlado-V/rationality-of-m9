module

public import StacksFrontier.LinearAlgebra.UnitalRowKernel
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-! Finite-sum linear algebra for the genuine Euler coefficients and the
value/derivative tuple. All geometric identities are proved in the native
consumer; these lemmas only expand the actual elementary kernel vectors. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000

open Module
open scoped BigOperators

universe u v w

namespace M9Native.MukaiConormalLinearJets

variable (K : Type u) [Field K]
variable {T : Type v} [AddCommGroup T] [Module K T]
variable {A : Type w} [AddCommGroup A] [Module K A]

def valueMap (v : Fin 14 → K) : (Fin 14 → K) →ₗ[K] K where
  toFun w := ∑ j : Fin 14, w j * v j
  map_add' w z := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a w := by simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul,
    mul_assoc, Finset.mul_sum]

def derivativeMap (d : Fin 14 → T) : (Fin 14 → K) →ₗ[K] T where
  toFun w := ∑ j : Fin 14, w j • d j
  map_add' w z := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a w := by simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul,
    mul_smul, Finset.smul_sum]

@[simp] theorem valueMap_single (v : Fin 14 → K) (i : Fin 14) :
    valueMap K v (Pi.single i 1) = v i := by simp [valueMap, Pi.single_apply]

@[simp] theorem derivativeMap_single (d : Fin 14 → T) (i : Fin 14) :
    derivativeMap K d (Pi.single i 1) = d i := by simp [derivativeMap, Pi.single_apply]

theorem valueMap_kernelGen (v r : Fin 14 → K) (i j : Fin 14) :
    valueMap K v (Stacks.LinearAlgebra.kernelGen r i j) = v j - r j * v i := by
  rw [Stacks.LinearAlgebra.kernelGen, map_sub, map_smul, valueMap_single, valueMap_single,
    smul_eq_mul]

theorem derivativeMap_kernelGen (d : Fin 14 → T) (r : Fin 14 → K) (i j : Fin 14) :
    derivativeMap K d (Stacks.LinearAlgebra.kernelGen r i j) = d j - r j • d i := by
  rw [Stacks.LinearAlgebra.kernelGen, map_sub, map_smul, derivativeMap_single, derivativeMap_single]

/-- The genuine ratio-basis coefficient expansion, retaining the actual
pivot's complement as its index type. -/
def eulerMap (r : Fin 14 → K) (i : Fin 14) (b : Basis {j : Fin 14 // j ≠ i} K A) :
    A →ₗ[K] (Fin 14 → K) :=
  ∑ j : {j : Fin 14 // j ≠ i}, (b.coord j).smulRight (Stacks.LinearAlgebra.kernelGen r i j.1)

@[simp] theorem eulerMap_basis (r : Fin 14 → K) (i : Fin 14)
    (b : Basis {j : Fin 14 // j ≠ i} K A) (j : {j : Fin 14 // j ≠ i}) :
    eulerMap K r i b (b j) = Stacks.LinearAlgebra.kernelGen r i j.1 := by
  simp [eulerMap, Module.Basis.coord_apply,Finsupp.single_apply]

theorem valueMap_comp_eulerMap (v r : Fin 14 → K) (i : Fin 14)
    (b : Basis {j : Fin 14 // j ≠ i} K A) (h : ∀ j, v j = r j * v i) :
    (valueMap K v).comp (eulerMap K r i b) = 0 := by
  apply b.ext
  intro j
  rw [LinearMap.comp_apply, eulerMap_basis, valueMap_kernelGen, h j.1, sub_self]
  rfl

theorem derivativeMap_comp_eulerMap (d : Fin 14 → T) (r : Fin 14 → K) (i : Fin 14)
    (b : Basis {j : Fin 14 // j ≠ i} K A) (δ : A →ₗ[K] T) (a : K)
    (h : ∀ j : {j : Fin 14 // j ≠ i}, d j.1 - r j.1 • d i = a • δ (b j)) :
    (derivativeMap K d).comp (eulerMap K r i b) = a • δ := by
  apply b.ext
  intro j
  rw [LinearMap.comp_apply, eulerMap_basis, derivativeMap_kernelGen]
  exact h j

theorem valueMap_surjective (v : Fin 14 → K) (i : Fin 14) (hi : v i ≠ 0) :
    Function.Surjective (valueMap K v) := by
  intro c
  refine ⟨(c / v i) • Pi.single i 1, ?_⟩
  rw [map_smul, valueMap_single, smul_eq_mul, div_mul_cancel₀ _ hi]

/-- A kernel adjustment changes the derivative arbitrarily while keeping
the value. This proves surjectivity of the actual paired first-jet map. -/
theorem prod_surjective_of_adjuster {D : Type*} [AddCommGroup D] [Module K D]
    (v : D →ₗ[K] K) (d : D →ₗ[K] T) (e : A →ₗ[K] D) (δ : A →ₗ[K] T)
    (a : K) (ha : a ≠ 0) (hv : Function.Surjective v) (hδ : Function.Surjective δ)
    (he₁ : v.comp e = 0) (he₂ : d.comp e = a • δ) :
    Function.Surjective (v.prod d) := by
  rintro ⟨c,t⟩
  obtain ⟨w,hw⟩ := hv c
  obtain ⟨x,hx⟩ := hδ (a⁻¹ • (t - d w))
  refine ⟨w + e x, Prod.ext ?_ ?_⟩
  · have hz : v (e x) = 0 := congrArg (fun f : A →ₗ[K] K => f x) he₁
    change v (w + e x) = c
    rw [map_add,hz,hw,add_zero]
  · have hz : d (e x) = a • δ x := congrArg (fun f : A →ₗ[K] T => f x) he₂
    change d (w + e x) = t
    rw [map_add,hz,hx,smul_smul,mul_inv_cancel₀ ha,one_smul,add_comm,sub_add_cancel]

end M9Native.MukaiConormalLinearJets
