module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! An actual linear evaluation of rank at most two factors through
a SURJECTIVE two-dimensional quotient of its original source. The
quotient and both maps are constructed from the actual kernel. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

universe u v w

namespace M9Native.RankTwoQuotientFactor

open Module

theorem exists_surjective_factor
    {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {W : Type w} [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (hV : 2 ≤ Module.finrank K V)
    (hf : Module.finrank K (LinearMap.range f) ≤ 2) :
    ∃ (q : V →ₗ[K] (Fin 2 → K)) (g : (Fin 2 → K) →ₗ[K] W),
      Function.Surjective q ∧ g.comp q = f := by
  classical
  have hnull := f.finrank_range_add_finrank_ker
  have hk : Module.finrank K V - 2 ≤ Module.finrank K (LinearMap.ker f) := by omega
  obtain ⟨v,hv⟩ := exists_linearIndependent_of_le_finrank hk
  let v' : Fin (Module.finrank K V - 2) → V := fun i => v i
  have hv' : LinearIndependent K v' :=
    hv.map' (LinearMap.ker f).subtype (by simp)
  let N := Submodule.span K (Set.range v')
  have hN : N ≤ LinearMap.ker f := by
    apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    exact (v i).property
  have hNdim : Module.finrank K N = Module.finrank K V - 2 := by
    simpa only [N, finrank_span_eq_card hv', Fintype.card_fin]
  have hQdim : Module.finrank K (V ⧸ N) = 2 := by
    have h := N.finrank_quotient_add_finrank
    rw [hNdim] at h
    omega
  let e : (V ⧸ N) ≃ₗ[K] (Fin 2 → K) :=
    (Module.finBasisOfFinrankEq K (V ⧸ N) hQdim).equivFun
  let q := e.toLinearMap.comp N.mkQ
  let g := (N.liftQ f hN).comp e.symm.toLinearMap
  refine ⟨q,g,e.surjective.comp N.mkQ_surjective,?_⟩
  ext x
  change N.liftQ f hN (e.symm (e (N.mkQ x))) = f x
  rw [e.symm_apply_apply]
  rfl

end M9Native.RankTwoQuotientFactor
