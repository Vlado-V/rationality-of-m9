module

public import M9.PrimitiveOpenOrbit
public import M9StacksIntegration.FractionDerivation
public import M9StacksIntegration.JacobianIndependence
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! The actual thirteen rational coordinates of the transverse symplectic Gauss family.
Their algebraic independence is deduced from the proved determinant `-2` at the identity. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9Native.PrimitiveGaussCoordinates

open MvPolynomial M9.PrimitiveOpenOrbit

variable (K : Type*) [Field K]

abbrev polynomial := ParameterRing K
abbrev rationalField := FractionRing (polynomial K)

def coordinate (j : Fin 13) : rationalField K :=
  algebraMap (polynomial K) (rationalField K) (formalTarget K j) /
    algebraMap (polynomial K) (rationalField K) (formalA K)

def coordinateDerivation (i : Fin 13) : Derivation K (rationalField K) (rationalField K) :=
  FractionDerivation.extend (pderiv i)

theorem coordinate_derivative (i j : Fin 13) :
    coordinateDerivation K i (coordinate K j) =
      (algebraMap (polynomial K) (rationalField K) (formalA K))⁻¹ ^ 2 *
        algebraMap (polynomial K) (rationalField K) (chartJacobian K j i) := by
  rw [coordinate, Derivation.leibniz_div]
  simp only [coordinateDerivation, FractionDerivation.extend_algebraMap, smul_eq_mul,
    chartJacobian, Matrix.of_apply, map_sub, map_mul]

theorem formalA_ne_zero : formalA K ≠ 0 := by
  intro h
  have he := evalBase_formalA K
  rw [h, map_zero] at he
  exact zero_ne_one he

def localizer : polynomial K := X 0 * formalA K

theorem localizer_ne_zero : localizer K ≠ 0 :=
  mul_ne_zero (X_ne_zero 0) (formalA_ne_zero K)

abbrev sourceRing := Localization.Away (localizer K)

instance sourceRing_isDomain : IsDomain (sourceRing K) :=
  Localization.Away.isDomain (localizer_ne_zero K)

theorem formalA_unit : IsUnit (algebraMap (polynomial K) (sourceRing K) (formalA K)) := by
  apply IsLocalization.Away.isUnit_of_dvd (localizer K)
  exact dvd_mul_left _ _

theorem parameter_unit : IsUnit (algebraMap (polynomial K) (sourceRing K) (X 0)) := by
  apply IsLocalization.Away.isUnit_of_dvd (localizer K)
  exact dvd_mul_right _ _

def inverseA : sourceRing K := ↑(formalA_unit K).unit⁻¹

theorem inverseA_mul :
    inverseA K * algebraMap (polynomial K) (sourceRing K) (formalA K) = 1 := by
  simpa only [inverseA, (formalA_unit K).unit_spec] using
    Units.inv_mul (formalA_unit K).unit

def sourceCoordinate (j : Fin 13) : sourceRing K :=
  inverseA K * algebraMap (polynomial K) (sourceRing K) (formalTarget K j)

def toRational : sourceRing K →+* rationalField K :=
  IsLocalization.Away.lift (localizer K)
    (g := algebraMap (polynomial K) (rationalField K))
    (isUnit_iff_ne_zero.mpr (by
      simpa only [map_zero] using
        (IsFractionRing.injective (polynomial K) (rationalField K)).ne (localizer_ne_zero K)))

@[simp] theorem toRational_algebraMap (p : polynomial K) :
    toRational K (algebraMap (polynomial K) (sourceRing K) p) =
      algebraMap (polynomial K) (rationalField K) p :=
  IsLocalization.Away.lift_eq _ _ p

theorem toRational_inverseA :
    toRational K (inverseA K) =
      (algebraMap (polynomial K) (rationalField K) (formalA K))⁻¹ := by
  have h := congrArg (toRational K) (inverseA_mul K)
  rw [map_mul, map_one, toRational_algebraMap] at h
  exact eq_inv_of_mul_eq_one_left h

@[simp] theorem toRational_sourceCoordinate (j : Fin 13) :
    toRational K (sourceCoordinate K j) = coordinate K j := by
  rw [sourceCoordinate, map_mul, toRational_inverseA, toRational_algebraMap,
    coordinate, div_eq_mul_inv, mul_comm]

def toRationalAlgHom : sourceRing K →ₐ[K] rationalField K where
  __ := toRational K
  commutes' c := by
    change toRational K (algebraMap K (sourceRing K) c) = _
    rw [IsScalarTower.algebraMap_apply K (polynomial K) (sourceRing K), toRational_algebraMap]
    exact (IsScalarTower.algebraMap_apply K (polynomial K) (rationalField K) c).symm

def coordinateMap : polynomial K →ₐ[K] sourceRing K := aeval (sourceCoordinate K)

theorem toRational_coordinateMap :
    (toRationalAlgHom K).comp (coordinateMap K) = aeval (coordinate K) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [coordinateMap, toRationalAlgHom]

variable [CharZero K]

theorem coordinate_algebraicIndependent : AlgebraicIndependent K (coordinate K) := by
  apply JacobianIndependence.algebraicIndependent_of_derivations (coordinateDerivation K)
  have hd : algebraMap (polynomial K) (rationalField K) (formalA K) ≠ 0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective (polynomial K) (rationalField K)).ne (formalA_ne_zero K)
  have hM : Matrix.of (fun i j => coordinateDerivation K i (coordinate K j)) =
      ((algebraMap (polynomial K) (rationalField K) (formalA K))⁻¹ ^ 2) •
        (chartJacobian K).transpose.map (algebraMap (polynomial K) (rationalField K)) := by
    ext i j
    exact coordinate_derivative K i j
  rw [hM, Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    Matrix.det_transpose]
  refine mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ (inv_ne_zero hd))) ?_
  simpa only [map_zero] using
    (IsFractionRing.injective (polynomial K) (rationalField K)).ne
      (chartJacobian_det_ne_zero K)

/-- The literal parameter homomorphism is injective; this is the dominance input. -/
theorem coordinateMap_injective : Function.Injective (coordinateMap K) := by
  have hinj : Function.Injective ((toRationalAlgHom K).comp (coordinateMap K)) := by
    rw [toRational_coordinateMap]
    exact coordinate_algebraicIndependent K
  intro p q hpq
  apply hinj
  change toRationalAlgHom K (coordinateMap K p) = toRationalAlgHom K (coordinateMap K q)
  rw [hpq]

end M9Native.PrimitiveGaussCoordinates
