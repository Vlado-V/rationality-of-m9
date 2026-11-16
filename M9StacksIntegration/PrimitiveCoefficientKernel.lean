module

public import M9StacksIntegration.PrimitiveCoefficientMatrices

/-! Coefficient kernels under actual changes of basis. The pairing uses
literal basis and dual-basis coefficients; no bilinear identification is
substituted for the dual action. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000

open Module Matrix
open scoped BigOperators

universe u v w x

namespace M9Native.PrimitiveCoefficientKernel

variable {K : Type u} [Field K] {V : Type v} [AddCommMonoid V] [Module K V]
  {W : Type w} [AddCommMonoid W] [Module K W]
  {I : Type x} [Fintype I] [DecidableEq I]

def coefficientMap (b : Basis I K V) (v : I → W) : Module.Dual K V →ₗ[K] W where
  toFun ell := ∑ i, ell (b i) • v i
  map_add' ell ell' := by
    simp only [LinearMap.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' a ell := by
    simp only [LinearMap.smul_apply,smul_smul,Finset.smul_sum,RingHom.id_apply,smul_eq_mul]

theorem coefficientMap_apply (b : Basis I K V) (v : I → W) (ell : Module.Dual K V) :
    coefficientMap b v ell = ∑ i, ell (b i) • v i := rfl

/-- Applying the vector matrix to a tuple is adjoint to the literal dual
map on its coefficient forms. -/
theorem coefficientMap_matrix (b : Basis I K V) (a : V ≃ₗ[K] V)
    (v : I → W) (ell : Module.Dual K V) :
    coefficientMap b
        (fun i => ∑ j, LinearMap.toMatrix b b a.toLinearMap i j • v j) ell =
      coefficientMap b v (a.dualMap ell) := by
  have h (j : I) : (a.dualMap ell) (b j) =
      ∑ i, LinearMap.toMatrix b b a.toLinearMap i j * ell (b i) := by
    change ell (a (b j)) = _
    conv_lhs => rw [← b.sum_repr (a (b j))]
    simp only [map_sum,map_smul,smul_eq_mul,LinearMap.toMatrix_apply,
      LinearEquiv.coe_toLinearMap]
  rw [coefficientMap_apply,coefficientMap_apply]
  simp only [Finset.smul_sum,h,Finset.sum_smul,mul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  exact smul_comm _ _ _

/-- A coefficient kernel transforms by the inverse dual, with no rank
or kernel-equality hypothesis. -/
theorem ker_coefficientMap_matrix (b : Basis I K V) (a : V ≃ₗ[K] V)
    (v : I → W) :
    LinearMap.ker (coefficientMap b
        (fun i => ∑ j, LinearMap.toMatrix b b a.toLinearMap i j • v j)) =
      (LinearMap.ker (coefficientMap b v)).map a.symm.dualMap.toLinearMap := by
  ext ell
  constructor
  · intro hell
    refine ⟨a.dualMap ell, ?_, ?_⟩
    · change coefficientMap b v (a.dualMap ell) = 0
      rw [← coefficientMap_matrix]
      exact hell
    · apply LinearMap.ext
      intro x
      change ell (a (a.symm x)) = ell x
      rw [LinearEquiv.apply_symm_apply]
  · rintro ⟨ell, hell, rfl⟩
    change coefficientMap b
      (fun i => ∑ j, LinearMap.toMatrix b b a.toLinearMap i j • v j)
        (a.symm.dualMap ell) = 0
    rw [coefficientMap_matrix]
    have h : a.dualMap (a.symm.dualMap ell) = ell := by
      apply LinearMap.ext
      intro x
      change ell (a.symm (a x)) = ell x
      rw [LinearEquiv.symm_apply_apply]
    rw [h]
    exact hell

end M9Native.PrimitiveCoefficientKernel
