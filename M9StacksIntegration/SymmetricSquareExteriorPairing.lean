module

public import M9StacksIntegration.SymmetricSquareDeterminantNaturality
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! Actual determinant evaluation and its original semilinear naturality. -/

@[expose] public noncomputable section

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open scoped TensorProduct

namespace M9Native.SymmetricSquareExteriorPairing

variable {R S M N A B : Type*} [CommRing R] [CommRing S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module S B]

/-- Induction on actual exterior vectors using their genuine spanning pure wedges. -/
theorem exteriorInduction (n : ℕ) (P : (⋀[R]^n M) → Prop)
    (hzero : P 0) (hpure : ∀ v : Fin n → M, P (exteriorPower.ιMulti R n v))
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hsmul : ∀ (r : R) x, P x → P (r • x)) (x : ⋀[R]^n M) : P x := by
  have hx : x ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n)) := by
    rw [exteriorPower.ιMulti_span]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨v, rfl⟩ := hy; exact hpure v
  | zero => exact hzero
  | add x y _ _ hx hy => exact hadd x y hx hy
  | smul r x _ hx => exact hsmul r x hx

/-- Any actual pairing compatible with the original scalar and vector maps
induces the corresponding determinant-pairing compatibility. -/
theorem pairing_semilinear (φ : R →+* S) (f : M →ₛₗ[φ] N) (g : A →ₛₗ[φ] B)
    (d : A →ₗ[R] Module.Dual R M) (e : B →ₗ[S] Module.Dual S N)
    (h : ∀ a m, e (g a) (f m) = φ (d a m))
    (n : ℕ) (x : ⋀[R]^n A) (y : ⋀[R]^n M) :
    exteriorPower.pairingDual S N n
        (exteriorPower.map n e (ExteriorAlgebra.powMapₛₗ n φ g x))
        (ExteriorAlgebra.powMapₛₗ n φ f y) =
      φ (exteriorPower.pairingDual R M n (exteriorPower.map n d x) y) := by
  apply exteriorInduction n (M := A)
    (P := fun x => exteriorPower.pairingDual S N n
      (exteriorPower.map n e (ExteriorAlgebra.powMapₛₗ n φ g x))
      (ExteriorAlgebra.powMapₛₗ n φ f y) =
        φ (exteriorPower.pairingDual R M n (exteriorPower.map n d x) y))
  · simp only [map_zero, LinearMap.zero_apply]
  · intro a
    apply exteriorInduction n (M := M)
      (P := fun y => exteriorPower.pairingDual S N n
        (exteriorPower.map n e (ExteriorAlgebra.powMapₛₗ n φ g (exteriorPower.ιMulti R n a)))
        (ExteriorAlgebra.powMapₛₗ n φ f y) =
          φ (exteriorPower.pairingDual R M n
            (exteriorPower.map n d (exteriorPower.ιMulti R n a)) y))
    · simp only [map_zero]
    · intro v
      simp only [ExteriorAlgebra.powMapₛₗ_ιMulti, exteriorPower.map_apply_ιMulti,
        exteriorPower.pairingDual_ιMulti_ιMulti]
      rw [φ.map_det]
      congr 1
      ext i j
      exact h (a j) (v i)
    · intro y z hy hz
      simp only [map_add, hy, hz]
    · intro r y hy
      simpa only [map_smulₛₗ, map_smul, smul_eq_mul, map_mul, RingHom.id_apply] using congrArg (φ r * ·) hy
  · intro x z hx hz
    simp only [map_add, LinearMap.add_apply, hx, hz]
  · intro r x hx
    simpa only [map_smulₛₗ, map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply]
      using congrArg (φ r * ·) hx

end M9Native.SymmetricSquareExteriorPairing
