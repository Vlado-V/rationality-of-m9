module

public import M9StacksIntegration.FiniteRankQuotientFactor
public import M9StacksIntegration.Sp6VectorTransitivity

/-!
# Actual rank-one original-six maps have an original symplectic functional

The coefficient functional and its nonzero original vector are derived
from the actual map and the original nondegenerate symplectic form. There
is no chosen functional, hyperplane, symplectic vector, or factorization
premise. The target is any original coefficient-field module.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v

namespace M9Native.SymplecticRankOneFactor

open Module M9Native.LagrangianRing

theorem exists_original_vector_factor
    (K : Type u) [Field K] {W : Type v} [AddCommGroup W] [Module K W]
    (θ : (Fin 6 → K) →ₗ[K] W)
    (hθ : Module.finrank K (LinearMap.range θ) ≤ 1) :
    ∃ (v : Fin 6 → K), v ≠ 0 ∧ ∃ z : W,
      ∀ w : Fin 6 → K, θ w = (omega K v w) • z := by
  classical
  obtain ⟨q,g,hq,hfactor⟩ := FiniteRankQuotientFactor.exists_surjective_factor
    1 θ (by simp) hθ
  let coeff : Module.Dual K (Fin 6 → K) := (LinearMap.proj (0 : Fin 1)).comp q
  have hcoeff : coeff ≠ 0 := by
    intro hz
    obtain ⟨w,hw⟩ := hq (fun _ => 1)
    have hh := LinearMap.congr_fun hz w
    change q w 0 = 0 at hh
    rw [hw] at hh
    exact one_ne_zero hh
  let e := (omega K).toDual (Sp6VectorTransitivity.omega_nondegenerate K)
  let v := e.symm coeff
  have hv : v ≠ 0 := by
    intro hz
    apply hcoeff
    calc
      coeff = e v := (e.apply_symm_apply coeff).symm
      _ = 0 := by rw [hz, map_zero]
  refine ⟨v,hv,g (fun _ => 1),?_⟩
  intro w
  have he : omega K v w = coeff w := LinearMap.congr_fun (e.apply_symm_apply coeff) w
  have hqval : q w = (coeff w) • (fun _ : Fin 1 => (1 : K)) := by
    funext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    simp [coeff]
  calc
    θ w = g (q w) := (LinearMap.congr_fun hfactor w).symm
    _ = (coeff w) • g (fun _ => 1) := by rw [hqval, map_smul]
    _ = (omega K v w) • g (fun _ => 1) := by rw [he]

end M9Native.SymplecticRankOneFactor
