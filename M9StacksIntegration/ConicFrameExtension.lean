module

public import M9StacksIntegration.ConicFrameSourceAlgebra
public import M9StacksIntegration.GenericEtaleFibreDegree
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! The genuine fraction-field extension attached to the injective
conic-frame coordinate homomorphism. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace M9Native.ConicFrameExtension

open M9Native.ConicFrameProjective M9Native.ConicFrameCoordinates
open M9Native.ConicFrameCoordinateIndex M9Native.ConicFrameSourceAlgebra

variable (K : Type u) [Field K]

instance coordinateAlgebra : Algebra (targetRing K) (sourceRing K) :=
  (coordinateMap K).toRingHom.toAlgebra

instance coordinateTower : IsScalarTower K (targetRing K) (sourceRing K) := by
  apply IsScalarTower.of_algebraMap_eq'
  exact (coordinateMap K).comp_algebraMap.symm

instance sourceFractionAlgebra : Algebra (sourceRing K) (rationalField K) :=
  (toRational K).toAlgebra

instance polynomialSourceFractionTower :
    IsScalarTower (polynomial K) (sourceRing K) (rationalField K) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro p
  exact (toRational_algebraMap K p).symm

instance sourceFractionTower : IsScalarTower K (sourceRing K) (rationalField K) := by
  apply IsScalarTower.of_algebraMap_eq'
  exact (toRationalAlgHom K).comp_algebraMap.symm

instance source_isFractionRing : IsFractionRing (sourceRing K) (rationalField K) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (localizer K)) (sourceRing K) (rationalField K)

instance coordinateFractionAlgebra : Algebra (targetRing K) (rationalField K) :=
  ((toRationalAlgHom K).comp (coordinateMap K)).toRingHom.toAlgebra

instance coordinateFractionTower : IsScalarTower K (targetRing K) (rationalField K) := by
  apply IsScalarTower.of_algebraMap_eq'
  exact ((toRationalAlgHom K).comp (coordinateMap K)).comp_algebraMap.symm

instance coordinateSourceFractionTower :
    IsScalarTower (targetRing K) (sourceRing K) (rationalField K) :=
  IsScalarTower.of_algebraMap_eq' rfl

instance target_finiteType : Algebra.FiniteType K (targetRing K) := inferInstanceAs
  (Algebra.FiniteType K (MvPolynomial _ K))

instance source_finiteType : Algebra.FiniteType K (sourceRing K) := by
  infer_instance

abbrev targetField := FractionRing (targetRing K)

variable [CharZero K]

theorem coordinateFraction_injective :
    Function.Injective (((toRationalAlgHom K).comp (coordinateMap K)) : targetRing K → rationalField K) := by
  rw [toRational_coordinateMap]
  exact (coordinate_algebraicIndependent K).comp coordinateEquiv coordinateEquiv.injective

/-- This embedding extends the literal quotient-coordinate homomorphism. -/
def targetFieldEmbedding : targetField K →ₐ[K] rationalField K :=
  IsFractionRing.liftAlgHom (coordinateFraction_injective K)

@[simp] theorem targetFieldEmbedding_algebraMap (p : targetRing K) :
    targetFieldEmbedding K (algebraMap (targetRing K) (targetField K) p) =
      toRationalAlgHom K (coordinateMap K p) :=
  IsFractionRing.lift_algebraMap (coordinateFraction_injective K) p

instance targetFieldAlgebra : Algebra (targetField K) (rationalField K) :=
  (targetFieldEmbedding K).toRingHom.toAlgebra

instance targetFieldTower : IsScalarTower K (targetField K) (rationalField K) := by
  apply IsScalarTower.of_algebraMap_eq'
  exact (targetFieldEmbedding K).comp_algebraMap.symm

instance coordinateTargetFieldTower :
    IsScalarTower (targetRing K) (targetField K) (rationalField K) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro p
  exact (targetFieldEmbedding_algebraMap K p).symm

omit [CharZero K] in
theorem targetField_trdeg : Algebra.trdeg K (targetField K) = 8 := by
  have : Algebra.IsAlgebraic (targetRing K) (targetField K) :=
    IsLocalization.isAlgebraic (targetField K) (nonZeroDivisors (targetRing K))
  have h := trdeg_add_eq K (targetRing K) (A := targetField K)
  rw [trdeg_eq_zero (R := targetRing K) (A := targetField K),add_zero] at h
  rw [← h]
  have hcard : Fintype.card (AlgebraicGeometry.Grassmannian.ChartIndex.{u}
      (k := 4) (n := 6) pivotEmbedding) = 8 := by
    simpa only [Fintype.card_fin] using Fintype.card_congr coordinateEquiv
  simp only [targetRing,MvPolynomial.trdeg_of_isDomain,Cardinal.mk_fintype,hcard]
  simp

omit [CharZero K] in
theorem rationalField_trdeg : Algebra.trdeg K (rationalField K) = 8 := by
  have : Algebra.IsAlgebraic (polynomial K) (rationalField K) :=
    IsLocalization.isAlgebraic (rationalField K) (nonZeroDivisors (polynomial K))
  have h := trdeg_add_eq K (polynomial K) (A := rationalField K)
  rw [trdeg_eq_zero (R := polynomial K) (A := rationalField K),add_zero] at h
  rw [← h]
  simp [polynomial,MvPolynomial.trdeg_of_isDomain]

instance targetField_isSeparable : Algebra.IsSeparable (targetField K) (rationalField K) :=
  GenericEtaleFibreDegree.isSeparable_of_equal_finite_trdeg K (targetField K) (rationalField K)
    (by rw [targetField_trdeg]; exact Cardinal.ofNat_lt_aleph0)
    (by rw [targetField_trdeg,rationalField_trdeg])

/-- Actual closed-fibre cardinalities suffice: the generic finite/étale
localization and the field degree are both derived by the checked provider. -/
theorem finite_degree_of_pointLifts_card [IsAlgClosed K] (N : ℕ) (hN : 0 < N)
    (hcard : ∀ x : targetRing K →ₐ[K] K,
      Nonempty (GenericEtaleFibreDegree.PointLifts K (targetRing K) (sourceRing K) x) →
      Nat.card (GenericEtaleFibreDegree.PointLifts K (targetRing K) (sourceRing K) x) = N) :
    Module.Finite (targetField K) (rationalField K) ∧
      Module.finrank (targetField K) (rationalField K) = N :=
  GenericEtaleFibreDegree.finite_and_fraction_finrank_eq_of_nonempty_pointLifts_card
    K (targetRing K) (sourceRing K) (targetField K) (rationalField K)
    (coordinateMap_injective K) N hN hcard

end M9Native.ConicFrameExtension
