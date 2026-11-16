module

public import M9StacksIntegration.ConicFrameCoordinates
public import M9StacksIntegration.ConicFrameCoordinateIndex
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! The actual coordinate homomorphism of the conic-frame map on a
Gamma-stable frame chart. Every first-row entry is nonzero, so all
twenty-four normalized right translates stay in this chart. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace M9Native.ConicFrameSourceAlgebra

open M9Native.ConicFrameProjective M9Native.ConicFrameCoordinates
open M9Native.ConicFrameCoordinateIndex

variable (K : Type u) [Field K]

abbrev targetRing := MvPolynomial (AlgebraicGeometry.Grassmannian.ChartIndex.{u}
  (k := 4) (n := 6) pivotEmbedding) K

def localizer : polynomial K :=
  (normalizedFrame K).det * denominator K * MvPolynomial.X 0 * MvPolynomial.X 1

theorem localizer_ne_zero : localizer K ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero (normalizedFrame_det_ne_zero K)
    (denominator_ne_zero K)) (MvPolynomial.X_ne_zero 0)) (MvPolynomial.X_ne_zero 1)

abbrev sourceRing := Localization.Away (localizer K)

instance sourceRing_isDomain : IsDomain (sourceRing K) := Localization.Away.isDomain (localizer_ne_zero K)

theorem denominator_unit : IsUnit (algebraMap (polynomial K) (sourceRing K) (denominator K)) := by
  apply IsLocalization.Away.isUnit_of_dvd (localizer K)
  refine ⟨(normalizedFrame K).det * MvPolynomial.X 0 * MvPolynomial.X 1,?_⟩
  simp only [localizer]
  ring

theorem frame_det_unit : IsUnit (algebraMap (polynomial K) (sourceRing K) (normalizedFrame K).det) := by
  apply IsLocalization.Away.isUnit_of_dvd (localizer K)
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _

def inverseDenominator : sourceRing K := ↑(denominator_unit K).unit⁻¹

theorem inverseDenominator_mul :
    inverseDenominator K * algebraMap (polynomial K) (sourceRing K) (denominator K) = 1 := by
  simpa only [inverseDenominator,(denominator_unit K).unit_spec] using
    Units.inv_mul (denominator_unit K).unit

def sourceCoordinate (j : Fin 8) : sourceRing K :=
  inverseDenominator K * algebraMap (polynomial K) (sourceRing K) (numerator K j)

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

theorem toRational_inverseDenominator :
    toRational K (inverseDenominator K) =
      (algebraMap (polynomial K) (rationalField K) (denominator K))⁻¹ := by
  have h := congrArg (toRational K) (inverseDenominator_mul K)
  rw [map_mul,map_one,toRational_algebraMap] at h
  exact eq_inv_of_mul_eq_one_left h

@[simp] theorem toRational_sourceCoordinate (j : Fin 8) :
    toRational K (sourceCoordinate K j) = coordinate K j := by
  rw [sourceCoordinate,map_mul,toRational_inverseDenominator,toRational_algebraMap,
    coordinate,div_eq_mul_inv,mul_comm]

/-- The field embedding agrees with the original coefficient-field algebra. -/
def toRationalAlgHom : sourceRing K →ₐ[K] rationalField K where
  __ := toRational K
  commutes' c := by
    change toRational K (algebraMap K (sourceRing K) c) = _
    rw [IsScalarTower.algebraMap_apply K (polynomial K) (sourceRing K),toRational_algebraMap]
    exact (IsScalarTower.algebraMap_apply K (polynomial K) (rationalField K) c).symm

/-- These are the actual nonpivot entries of the normalized quotient matrix. -/
def coordinateMap : targetRing K →ₐ[K] sourceRing K :=
  MvPolynomial.aeval (fun a => sourceCoordinate K (coordinateEquiv a))

theorem toRational_coordinateMap :
    (toRationalAlgHom K).comp (coordinateMap K) =
      MvPolynomial.aeval (fun a => coordinate K (coordinateEquiv a)) := by
  apply MvPolynomial.algHom_ext
  intro a
  simp [coordinateMap,toRationalAlgHom]

variable [CharZero K]

/-- Injectivity is proved from the literal Jacobian, not posited as dominance. -/
theorem coordinateMap_injective : Function.Injective (coordinateMap K) := by
  have hAI : AlgebraicIndependent K (fun a => coordinate K (coordinateEquiv a)) :=
    (coordinate_algebraicIndependent K).comp coordinateEquiv coordinateEquiv.injective
  have hinj : Function.Injective ((toRationalAlgHom K).comp (coordinateMap K)) := by
    rw [toRational_coordinateMap]
    exact hAI
  intro p q hpq
  apply hinj
  change toRationalAlgHom K (coordinateMap K p) = toRationalAlgHom K (coordinateMap K q)
  rw [hpq]

end M9Native.ConicFrameSourceAlgebra
