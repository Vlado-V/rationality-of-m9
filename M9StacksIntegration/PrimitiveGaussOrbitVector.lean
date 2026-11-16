module

public import M9StacksIntegration.PrimitiveGaussNativeOrbit
public import M9StacksIntegration.PrimitiveGaussEvaluation

/-! The universal Gauss-coordinate vector is the actual ring-valued primitive action on rho.
The identity holds in the localization itself, proved using its separating complex evaluations. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Matrix

namespace M9Native.PrimitiveGaussOrbitVector

open PrimitiveGaussCoordinates PrimitiveGaussEvaluation PrimitiveGaussNativeOrbit

def rhoCoordinates : Fin 14 → ℂ :=
  M9.PrimitiveRadicalScheme.primitiveCoordinates (M9.PrimitiveStabilizer.rho ℂ)

def orbitVector : Fin 14 → sourceRing ℂ :=
  PrimitiveRingCoordinates.primitiveMatrix (sourceRing ℂ) (algebraMap ℂ (sourceRing ℂ))
    (PrimitiveGaussFamily.family ℂ) *ᵥ (algebraMap ℂ (sourceRing ℂ) ∘ rhoCoordinates)

theorem evaluation_orbitVector (z : Fin 13 → ℂ)
    (hz : MvPolynomial.eval z (localizer ℂ) ≠ 0) :
    (fun i => evaluation z hz (orbitVector i)) =
      M9.PrimitiveRadicalScheme.primitiveCoordinates
        (M9.PrimitiveStabilizer.primitiveLinear ℂ
          (M9.PrimitiveOpenOrbit.gauss ℂ (z 0) (parameter_ne_zero z hz)
            (M9.PrimitiveOpenOrbit.upperParameterMatrix ℂ z)
            (M9.PrimitiveOpenOrbit.lowerParameterMatrix ℂ z))
          (M9.PrimitiveStabilizer.rho ℂ)) := by
  have hf : (evaluation z hz).toRingHom.comp (algebraMap ℂ (sourceRing ℂ)) = RingHom.id ℂ := by
    ext c
    exact (evaluation z hz).commutes c
  have hM := PrimitiveRingCoordinates.primitiveMatrix_map (sourceRing ℂ)
    (algebraMap ℂ (sourceRing ℂ)) (evaluation z hz).toRingHom (PrimitiveGaussFamily.family ℂ)
  rw [hf] at hM
  funext i
  rw [orbitVector]
  change (evaluation z hz).toRingHom ((PrimitiveRingCoordinates.primitiveMatrix
    (sourceRing ℂ) (algebraMap ℂ (sourceRing ℂ)) (PrimitiveGaussFamily.family ℂ) *ᵥ
      (algebraMap ℂ (sourceRing ℂ) ∘ rhoCoordinates)) i) = _
  rw [RingHom.map_mulVec]
  rw [← hM]
  have hr : (evaluation z hz).toRingHom ∘ (algebraMap ℂ (sourceRing ℂ) ∘ rhoCoordinates) =
      rhoCoordinates := by
    funext j
    exact (evaluation z hz).commutes _
  rw [hr]
  change (PrimitiveRingCoordinates.primitiveMatrix ℂ (RingHom.id ℂ)
    (evaluatedFamily z hz) *ᵥ rhoCoordinates) i = _
  rw [rhoCoordinates, PrimitiveRingFieldBridge.primitiveMatrix_coordinates,
    evaluatedFamily_toOriginal]

/-- Literal equality over the actual source coordinate ring, not just equality at field points. -/
theorem polynomialVector_eq_scaled_orbitVector :
    (fun i => algebraMap (polynomial ℂ) (sourceRing ℂ) (polynomialVector i)) =
      (algebraMap (polynomial ℂ) (sourceRing ℂ) (MvPolynomial.X 0)) ^ 3 • orbitVector := by
  funext i
  apply sub_eq_zero.mp
  apply eq_zero_of_evaluation
  intro z hz
  simp only [map_sub, Pi.smul_apply, smul_eq_mul, map_mul, map_pow,
    evaluation_algebraMap, MvPolynomial.eval_X]
  rw [sub_eq_zero]
  have hp := congrFun (eval_polynomialVector z (parameter_ne_zero z hz)) i
  have ho := congrFun (evaluation_orbitVector z hz) i
  rw [hp, ho]
  change M9.PrimitiveRadicalScheme.primitiveCoordinates
      ((z 0)^3 • M9.PrimitiveStabilizer.primitiveAction ℂ _ (M9.PrimitiveStabilizer.rho ℂ)) i = _
  rw [map_smul]
  rfl

end M9Native.PrimitiveGaussOrbitVector
