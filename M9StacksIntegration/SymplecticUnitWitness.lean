module

public import M9StacksIntegration.Sp6VectorTransitivity

/-! A nonzero original six-vector has a genuine original constant
symplectic partner of pairing one. No pairing witness is assumed. -/

@[expose] public noncomputable section
set_option autoImplicit false

open Module

universe u

namespace M9Native.SymplecticUnitWitness

open LagrangianRing

variable (K : Type u) [Field K] (v : Fin 6 → K) (hv : v ≠ 0)

include hv

theorem exists_pairing_one : ∃ w : Fin 6 → K, omega K v w = 1 := by
  classical
  have hn : ¬ ∀ w, omega K v w = 0 := fun hz =>
    hv ((Sp6VectorTransitivity.omega_nondegenerate K).1 v hz)
  obtain ⟨w,hw⟩ := not_forall.mp hn
  refine ⟨(omega K v w)⁻¹ • w,?_⟩
  rw [map_smul,smul_eq_mul,inv_mul_cancel₀ hw]

theorem pairing_surjective : Function.Surjective (omega K v) := by
  obtain ⟨w,hw⟩ := exists_pairing_one K v hv
  intro a
  exact ⟨a • w,by rw [map_smul,smul_eq_mul,hw,mul_one]⟩

end M9Native.SymplecticUnitWitness
end
