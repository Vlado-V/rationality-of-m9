module

public import M9StacksIntegration.MukaiConormalPrimitive
public import M9StacksIntegration.LagrangianSigmaInvariance
public import M9StacksIntegration.MukaiQuarticHitchin

/-!
# Canonical representatives of native primitive projective forms

The projector is the actual exterior operator `w − (1/2) sigma ∧ C(w)`.
Its formula, kernel and covariance are proved, rather than transferred
from a declared fourteen-coordinate representation. It gives the genuine
canonical representative of `Dual (ker contraction)`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open Module Matrix
open scoped BigOperators

namespace M9Native.MukaiPrimitiveProjector

open LagrangianField MukaiPrimitiveDuality MukaiConormalPrimitive
open MukaiQuarticExterior MukaiQuarticHitchin

variable (K : Type*) [Field K]

theorem wedgeMul_ιMulti {V : Type*} [AddCommGroup V] [Module K V]
    (m n : ℕ) (u : Fin m → V) (v : Fin n → V) :
    wedgeMul K m n (exteriorPower.ιMulti K m u) (exteriorPower.ιMulti K n v) =
      exteriorPower.ιMulti K (m+n) (Fin.append u v) := by
  apply Subtype.ext
  exact ExteriorAlgebra.ιMulti_mul_ιMulti (R := K) u v

theorem wedgeSigma_eq_product (v : V K) :
    wedgeSigma K v = wedgeMul K 2 1 (sigma K) (one K v) := by
  rw [wedgeSigma_apply, sigma]
  simp only [map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [one_ιMulti, wedgeMul_ιMulti]
  unfold wedge3
  congr 1
  funext j
  fin_cases j <;> rfl

theorem contraction_wedgeSigma (v : V K) :
    contraction K (wedgeSigma K v) = (2 : K) • v := by
  rw [wedgeSigma_apply, map_sum]
  simp only [contraction_wedge3]
  funext j
  fin_cases j <;>
    simp [omega, omegaValue, e, f, eIndex, fIndex, basisVector,
      Fin.sum_univ_succ, Pi.single_apply, smul_eq_mul] <;> ring

theorem contraction_map (g : V K →ₗ[K] V K)
    (hg : ∀ v w, omega K (g v) (g w) = omega K v w) (w : Third K) :
    contraction K (exteriorPower.map 3 g w) = g (contraction K w) := by
  have h : (contraction K).comp (exteriorPower.map 3 g) = g.comp (contraction K) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, contraction_ιMulti, contractionFormula, tripleContract,
      Function.comp_apply, hg, map_add, map_sub, map_smul]
  exact LinearMap.congr_fun h w

theorem wedgeSigma_map (g : V K →ₗ[K] V K)
    (hg : exteriorPower.map 2 g (sigma K) = sigma K) (v : V K) :
    exteriorPower.map 3 g (wedgeSigma K v) = wedgeSigma K (g v) := by
  rw [wedgeSigma_eq_product, wedgeMul_map K 2 1 g, hg, one_map, ← wedgeSigma_eq_product]

variable [CharZero K]

/-- The canonical projector, with the literal coefficient forced by the
proved contraction of the actual sigma-wedge. -/
def projector : Third K →ₗ[K] Third K :=
  LinearMap.id - (2 : K)⁻¹ • (wedgeSigma K).comp (contraction K)

omit [CharZero K] in
theorem projector_apply (w : Third K) :
    projector K w = w - (2 : K)⁻¹ • wedgeSigma K (contraction K w) := rfl

theorem contraction_projector (w : Third K) :
    contraction K (projector K w) = 0 := by
  rw [projector_apply, map_sub, map_smul, contraction_wedgeSigma, smul_smul,
    inv_mul_cancel₀ (two_ne_zero : (2 : K) ≠ 0), one_smul, sub_self]

theorem projector_wedgeSigma (v : V K) : projector K (wedgeSigma K v) = 0 := by
  rw [projector_apply, contraction_wedgeSigma, map_smul, smul_smul,
    inv_mul_cancel₀ (two_ne_zero : (2 : K) ≠ 0), one_smul, sub_self]

omit [CharZero K] in
theorem projector_of_primitive (w : Third K) (hw : contraction K w = 0) :
    projector K w = w := by simp [projector_apply, hw]

omit [CharZero K] in
theorem primitiveClass_projector (w : Third K) :
    primitiveClass K (projector K w) = primitiveClass K w := by
  simp only [projector_apply, map_sub, map_smul, primitiveClass_wedgeSigma,
    smul_zero, sub_zero]

omit [CharZero K] in
theorem projector_map (g : V K →ₗ[K] V K)
    (hω : ∀ v w, omega K (g v) (g w) = omega K v w)
    (hσ : exteriorPower.map 2 g (sigma K) = sigma K) (w : Third K) :
    projector K (exteriorPower.map 3 g w) = exteriorPower.map 3 g (projector K w) := by
  simp only [projector_apply, map_sub, map_smul, contraction_map K g hω,
    wedgeSigma_map K g hσ]

/-- The canonical representative is defined on the literal native
projective degree-one form module. -/
def representative : Module.Dual K (Primitive K) →ₗ[K] Third K :=
  factor K (projector K)

theorem representative_primitiveClass (w : Third K) :
    representative K (primitiveClass K w) = projector K w := by
  exact (factor_restriction K (projector K) (projector_wedgeSigma K)
    (coefficientDuality K w)).trans (by rw [LinearEquiv.symm_apply_apply])

theorem restriction_extension (ell : Module.Dual K (Primitive K)) :
    restriction K (extension K ell) = ell := by
  apply LinearMap.ext
  intro w
  change ell (primitiveProjection K w.val) = ell w
  congr 1
  apply Subtype.ext
  change coordinateEmbedding K (coordinateProjection K w.val) = w.val
  exact coordinateEmbedding_projection_of_primitive K w.val w.property

theorem primitiveClass_surjective : Function.Surjective (primitiveClass K) := by
  intro ell
  refine ⟨(coefficientDuality K).symm (extension K ell), ?_⟩
  change restriction K (coefficientDuality K ((coefficientDuality K).symm (extension K ell))) = ell
  rw [LinearEquiv.apply_symm_apply, restriction_extension]

theorem contraction_representative (ell : Module.Dual K (Primitive K)) :
    contraction K (representative K ell) = 0 := by
  obtain ⟨w, rfl⟩ := primitiveClass_surjective K ell
  rw [representative_primitiveClass, contraction_projector]

theorem primitiveClass_representative (ell : Module.Dual K (Primitive K)) :
    primitiveClass K (representative K ell) = ell := by
  obtain ⟨w, rfl⟩ := primitiveClass_surjective K ell
  rw [representative_primitiveClass, primitiveClass_projector]

theorem representative_injective : Function.Injective (representative K) := by
  intro u v h
  have hh := congrArg (primitiveClass K) h
  simpa only [primitiveClass_representative] using hh

end M9Native.MukaiPrimitiveProjector
