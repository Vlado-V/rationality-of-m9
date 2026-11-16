module

public import M9StacksIntegration.MukaiQuarticGradient
public import M9StacksIntegration.MukaiPrimitiveQuarticAction

/-! The actual gradient transforms contragrediently under the native
primitive action. In particular the normalized determinant formula is
transported to the literal transformed Plücker point, with its original
coefficient rather than an assumed proportionality scalar. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open Module Matrix

namespace M9Native.MukaiQuarticGradientTransport

open LagrangianField LagrangianSigmaInvariance PrimitiveCoefficientAction
open MukaiPrimitiveQuartic MukaiPrimitiveQuarticAction MukaiConormalPrimitive
open MukaiConormalOrigin MukaiQuarticGradient

variable (K : Type*) [Field K] [CharZero K]

abbrev formsAction (g : Matrix.symplecticGroup (Fin 3) K) : Forms K ≃ₗ[K] Forms K :=
  (primitiveAction K (transposeSymplectic K g)).dualMap

def transformedOrigin (g : Matrix.symplecticGroup (Fin 3) K) : Primitive K :=
  (primitiveAction K (transposeSymplectic K g)).symm (originPoint K)

theorem primitiveCubic_gradient_nativeAction (g : Matrix.symplecticGroup (Fin 3) K)
    (a b c : Forms K) :
    primitiveCubic K (formsAction K g a) (formsAction K g b) (formsAction K g c) =
      (primitiveCubic K a b c).comp (formsAction K g).symm.toLinearMap := by
  apply LinearMap.ext
  intro ell
  have h := primitiveCubic_nativeAction K g a b c ((formsAction K g).symm ell)
  change primitiveCubic K (formsAction K g a) (formsAction K g b) (formsAction K g c)
    (formsAction K g ((formsAction K g).symm ell)) = _ at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h

theorem primitiveCubic_transformed_conormalForm (g : Matrix.symplecticGroup (Fin 3) K)
    (c : K) (S : Symmetric3 K) :
    primitiveCubic K (formsAction K g (conormalForm K (c,S)))
      (formsAction K g (conormalForm K (c,S)))
      (formsAction K g (conormalForm K (c,S))) =
      (4*S.val.det) • Module.Dual.eval K (Primitive K) (transformedOrigin K g) := by
  rw [primitiveCubic_gradient_nativeAction, primitiveCubic_conormalForm_linear]
  apply LinearMap.ext
  intro ell
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul,
    Module.Dual.eval_apply, formsAction, LinearEquiv.dualMap_symm,
    transformedOrigin]
  rfl

theorem primitiveCubic_transformed_conormalForm_ne_zero
    (g : Matrix.symplecticGroup (Fin 3) K) (c : K) (S : Symmetric3 K) (hS : S.val.det ≠ 0) :
    primitiveCubic K (formsAction K g (conormalForm K (c,S)))
      (formsAction K g (conormalForm K (c,S)))
      (formsAction K g (conormalForm K (c,S))) ≠ 0 := by
  intro hz
  have h := LinearMap.congr_fun hz (formsAction K g (originFunctional K))
  rw [primitiveCubic_gradient_nativeAction, LinearMap.comp_apply] at h
  change primitiveCubic K (conormalForm K (c,S)) (conormalForm K (c,S))
    (conormalForm K (c,S))
      ((formsAction K g).symm (formsAction K g (originFunctional K))) = 0 at h
  rw [LinearEquiv.symm_apply_apply, primitiveCubic_conormalForm,
    originFunctional_origin, mul_one] at h
  exact mul_ne_zero (by norm_num : (4 : K) ≠ 0) hS h

end M9Native.MukaiQuarticGradientTransport
