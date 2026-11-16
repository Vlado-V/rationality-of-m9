module

public import M9StacksIntegration.PrimitiveGaussFamily
public import M9StacksIntegration.PrimitiveRingFieldBridge
public import Mathlib.Algebra.MvPolynomial.Funext

/-! Literal field evaluation and separation for the actual principal-open Gauss family. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 10000

open Matrix MvPolynomial

namespace M9Native.PrimitiveGaussEvaluation

open PrimitiveGaussCoordinates M9.PrimitiveOpenOrbit

def evaluation (z : Fin 13 → ℂ) (hz : MvPolynomial.eval z (localizer ℂ) ≠ 0) :
    sourceRing ℂ →ₐ[ℂ] ℂ :=
  IsLocalization.Away.liftAlgHom (localizer ℂ) (f := MvPolynomial.aeval z)
    (isUnit_iff_ne_zero.mpr hz)

@[simp] theorem evaluation_algebraMap (z : Fin 13 → ℂ)
    (hz : MvPolynomial.eval z (localizer ℂ) ≠ 0) (p : polynomial ℂ) :
    evaluation z hz (algebraMap (polynomial ℂ) (sourceRing ℂ) p) = MvPolynomial.eval z p := by
  simp [evaluation]

theorem parameter_ne_zero (z : Fin 13 → ℂ)
    (hz : MvPolynomial.eval z (localizer ℂ) ≠ 0) : z 0 ≠ 0 := by
  exact left_ne_zero_of_mul (show z 0 * MvPolynomial.eval z (formalA ℂ) ≠ 0 by
    simpa only [localizer, map_mul, MvPolynomial.eval_X] using hz)

theorem formalA_evaluation_ne_zero (z : Fin 13 → ℂ)
    (hz : MvPolynomial.eval z (localizer ℂ) ≠ 0) : MvPolynomial.eval z (formalA ℂ) ≠ 0 := by
  exact right_ne_zero_of_mul (show MvPolynomial.eval z (X 0) *
    MvPolynomial.eval z (formalA ℂ) ≠ 0 by simpa only [localizer, map_mul] using hz)

/-- The actual complex points of this reduced localization separate its elements. -/
theorem eq_zero_of_evaluation (r : sourceRing ℂ)
    (h : ∀ z (hz : MvPolynomial.eval z (localizer ℂ) ≠ 0), evaluation z hz r = 0) : r = 0 := by
  obtain ⟨p, s, hs⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers (localizer ℂ)) r
  have hp : p = 0 := by
    have he : p * localizer ℂ = 0 := by
      apply MvPolynomial.funext
      intro z
      rw [map_mul, map_zero]
      by_cases hz : MvPolynomial.eval z (localizer ℂ) = 0
      · rw [hz, mul_zero]
      · have hm := congrArg (evaluation z hz)
          (IsLocalization.mk'_spec (sourceRing ℂ) p s)
        rw [hs, map_mul, h z hz, zero_mul, evaluation_algebraMap] at hm
        rw [← hm, zero_mul]
    exact (mul_eq_zero.mp he).resolve_right (localizer_ne_zero ℂ)
  rw [← hs, hp, IsLocalization.mk'_zero]

def evaluatedFamily (z : Fin 13 → ℂ)
    (hz : MvPolynomial.eval z (localizer ℂ) ≠ 0) : Matrix.symplecticGroup (Fin 3) ℂ :=
  LagrangianTransitivity.mapSymplectic (sourceRing ℂ) (evaluation z hz).toRingHom
    (PrimitiveGaussFamily.family ℂ)

theorem evaluatedFamily_scaled (z : Fin 13 → ℂ)
    (hz : MvPolynomial.eval z (localizer ℂ) ≠ 0) :
    z 0 • LagrangianTransitivity.matrixSix ℂ (evaluatedFamily z hz) =
      gaussEntries (z 0) (upperParameters z) (lowerParameters z) := by
  rw [evaluatedFamily, LagrangianTransitivity.matrixSix_map]
  ext i j
  have he := congrArg (fun M : Matrix (Fin 6) (Fin 6) (sourceRing ℂ) =>
    evaluation z hz (M i j)) (PrimitiveGaussFamily.family_scaled ℂ)
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, evaluation_algebraMap,
    Matrix.map_apply, MvPolynomial.eval_X] at he
  exact he.trans (congrFun (congrFun (eval_formalMatrix ℂ z) i) j)

/-- The evaluated group-scheme family is the original literal symplectic Gauss transformation. -/
theorem evaluatedFamily_toOriginal (z : Fin 13 → ℂ)
    (hz : MvPolynomial.eval z (localizer ℂ) ≠ 0) :
    PrimitiveRingFieldBridge.toOriginal (evaluatedFamily z hz) =
      M9.PrimitiveOpenOrbit.gauss ℂ (z 0) (parameter_ne_zero z hz)
        (upperParameterMatrix ℂ z) (lowerParameterMatrix ℂ z) := by
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.toMatrix'.injective
  ext i j
  simp only [LinearMap.toMatrix'_apply]
  change (PrimitiveRingFieldBridge.toOriginal (evaluatedFamily z hz)).val (Pi.single j 1) i =
    (M9.PrimitiveOpenOrbit.gauss ℂ (z 0) (parameter_ne_zero z hz)
      (upperParameterMatrix ℂ z) (lowerParameterMatrix ℂ z)).val (Pi.single j 1) i
  rw [PrimitiveRingFieldBridge.toOriginal_apply, Matrix.mulVec_single_one]
  change LagrangianTransitivity.matrixSix ℂ (evaluatedFamily z hz) i j =
    (M9.PrimitiveOpenOrbit.gauss ℂ (z 0) (parameter_ne_zero z hz)
      (upperParameterMatrix ℂ z) (lowerParameterMatrix ℂ z)).val
        (M9.ExteriorPrimitive.basisVector ℂ j) i
  rw [gauss_apply]
  change LagrangianTransitivity.matrixSix ℂ (evaluatedFamily z hz) i j =
    (z 0)⁻¹ * scaledGauss ℂ (z 0) (upperParameterMatrix ℂ z)
      (lowerParameterMatrix ℂ z) (M9.ExteriorPrimitive.basisVector ℂ j) i
  rw [scaledGauss_entry]
  apply mul_left_cancel₀ (parameter_ne_zero z hz)
  rw [← mul_assoc, mul_inv_cancel₀ (parameter_ne_zero z hz), one_mul]
  exact congrFun (congrFun (evaluatedFamily_scaled z hz) i) j

end M9Native.PrimitiveGaussEvaluation
