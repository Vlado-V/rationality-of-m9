module

public import M9StacksIntegration.PrimitiveRhoOrbitDominance

/-! Literal linear functionals recover the thirteen Gauss orbit ratios from the fixed
fourteen coordinates, over every complex extension field. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Matrix

namespace M9Native.PrimitiveGaussFieldRatios

open PrimitiveGaussCoordinates PrimitiveGaussNativeOrbit PrimitiveGaussOrbitVector

def inverseCoordinates {R : Type*} [CommRing R] [Algebra ℂ R] : Matrix (Fin 14) (Fin 14) R :=
  (coordinateMatrix⁻¹).val.map (algebraMap ℂ R)

theorem inverseCoordinates_coordinateMatrix {R : Type*} [CommRing R] [Algebra ℂ R] :
    inverseCoordinates (R := R) * coordinateMatrix.val.map (algebraMap ℂ R) = 1 := by
  rw [inverseCoordinates,← Matrix.map_mul,Units.inv_mul]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem source_scaled :
    (algebraMap (polynomial ℂ) (sourceRing ℂ) (MvPolynomial.X 0))^3 •
      (inverseCoordinates *ᵥ orbitVector) =
      algebraMap (polynomial ℂ) (sourceRing ℂ) (M9.PrimitiveOpenOrbit.formalA ℂ) •
        PrimitiveRhoOrbitDominance.normalVector := by
  have he := polynomialVector_eq_scaled_orbitVector.symm.trans
    PrimitiveRhoOrbitDominance.polynomialVector_scaled
  have h := congrArg (fun v : Fin 14 → sourceRing ℂ => inverseCoordinates *ᵥ v) he
  rw [Matrix.mulVec_smul,Matrix.mulVec_smul] at h
  change _ = _ • (inverseCoordinates *ᵥ
    (coordinateMatrix.val.map (algebraMap ℂ (sourceRing ℂ)) *ᵥ
      PrimitiveRhoOrbitDominance.normalVector)) at h
  rw [Matrix.mulVec_mulVec,inverseCoordinates_coordinateMatrix,Matrix.one_mulVec] at h
  exact h

variable {K : Type} [Field K] [Algebra ℂ K]

def orbitAt (f : sourceRing ℂ →ₐ[ℂ] K) : Fin 14 → K := fun i => f (orbitVector i)

def normalAt (f : sourceRing ℂ →ₐ[ℂ] K) : Fin 14 → K := inverseCoordinates *ᵥ orbitAt f

theorem normalAt_scaled (f : sourceRing ℂ →ₐ[ℂ] K) (i : Fin 14) :
    (f (algebraMap (polynomial ℂ) (sourceRing ℂ) (MvPolynomial.X 0)))^3 * normalAt f i =
      f (algebraMap (polynomial ℂ) (sourceRing ℂ) (M9.PrimitiveOpenOrbit.formalA ℂ)) *
        (Fin.cons (1 : K) (fun j : Fin 13 => f (sourceCoordinate ℂ j)) : Fin 14 → K) i := by
  have h := congrArg (fun v : Fin 14 → sourceRing ℂ => f (v i)) source_scaled
  have hm : (inverseCoordinates (R := sourceRing ℂ)).map f.toRingHom = inverseCoordinates (R := K) := by
    ext j k
    exact f.commutes _
  have hc : f ((inverseCoordinates *ᵥ orbitVector) i) = normalAt f i := by
    change f.toRingHom ((inverseCoordinates *ᵥ orbitVector) i) = _
    rw [RingHom.map_mulVec,hm]
    rfl
  simp only [Pi.smul_apply,smul_eq_mul,map_mul,map_pow] at h
  rw [hc] at h
  have hn : f (PrimitiveRhoOrbitDominance.normalVector i) =
      (Fin.cons (1 : K) (fun j : Fin 13 => f (sourceCoordinate ℂ j)) : Fin 14 → K) i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact f.map_one
    · rfl
  exact h.trans (congrArg (fun a =>
    f (algebraMap (polynomial ℂ) (sourceRing ℂ) (M9.PrimitiveOpenOrbit.formalA ℂ)) * a) hn)

theorem normalAt_zero_ne_zero (f : sourceRing ℂ →ₐ[ℂ] K) : normalAt f 0 ≠ 0 := by
  have h := normalAt_scaled f 0
  simp only [Fin.cons_zero,mul_one] at h
  intro hz
  rw [hz,mul_zero] at h
  exact (isUnit_iff_ne_zero.mp ((formalA_unit ℂ).map f.toMonoidHom)) h.symm

theorem normalAt_ratio (f : sourceRing ℂ →ₐ[ℂ] K) (j : Fin 13) :
    normalAt f j.succ / normalAt f 0 = f (sourceCoordinate ℂ j) := by
  have h0 := normalAt_scaled f 0
  have hj := normalAt_scaled f j.succ
  simp only [Fin.cons_zero,mul_one] at h0
  simp only [Fin.cons_succ] at hj
  have ht : f (algebraMap (polynomial ℂ) (sourceRing ℂ) (MvPolynomial.X 0)) ≠ 0 :=
    isUnit_iff_ne_zero.mp ((parameter_unit ℂ).map f.toMonoidHom)
  apply (div_eq_iff (normalAt_zero_ne_zero f)).mpr
  apply mul_left_cancel₀ (pow_ne_zero 3 ht)
  rw [hj,← h0]
  ring

end M9Native.PrimitiveGaussFieldRatios
