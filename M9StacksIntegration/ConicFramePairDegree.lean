module

public import M9StacksIntegration.ConicFramePairRings
public import M9StacksIntegration.ConicFrameTensorPointFiber
public import M9StacksIntegration.ConicFrameExtension
public import Mathlib.RingTheory.FiniteStability
import all Mathlib.Basic.Complex.Basic
import all Mathlib.RingTheory.OreLocalization.Basic
import all Mathlib.Algebra.MonoidAlgebra.Defs

/-! The actual independent tensor-coordinate extension has degree 576.
The degree is derived from the actual tensor fibres; it is not an input. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

open scoped TensorProduct

namespace M9Native.ConicFramePairDegree

open ConicFramePairRings ConicFrameSourceAlgebra

abbrev A := targetPair ℂ
abbrev B := sourcePair ℂ
abbrev K := targetPairField ℂ
abbrev L := sourcePairField ℂ

@[instance_reducible] def coordinateAlgebra : Algebra A B :=
  ConicFrameTensorPointFiber.pairCoordinateAlgebra

theorem coordinateTower :
    letI := coordinateAlgebra
    IsScalarTower ℂ A B :=
  ConicFrameTensorPointFiber.pairCoordinateTower

@[instance_reducible] def coordinateFractionAlgebra : Algebra A L :=
  ((IsScalarTower.toAlgHom ℂ B L).comp (coordinatePairMap ℂ)).toRingHom.toAlgebra

@[instance_reducible] def actualFieldAlgebra : Algebra K L :=
  (pairFieldEmbedding ℂ).toRingHom.toAlgebra

instance targetField_charZero : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℂ K).injective

instance target_finiteType : Algebra.FiniteType ℂ A :=
  Algebra.FiniteType.trans (S := targetRing ℂ) inferInstance inferInstance

instance source_finiteType : Algebra.FiniteType ℂ B :=
  Algebra.FiniteType.trans (S := sourceRing ℂ) inferInstance inferInstance

theorem polynomial_fraction_trdeg (ι : Type) [Fintype ι] :
    Algebra.trdeg ℂ (FractionRing (MvPolynomial ι ℂ)) = Fintype.card ι := by
  have : Algebra.IsAlgebraic (MvPolynomial ι ℂ) (FractionRing (MvPolynomial ι ℂ)) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial ι ℂ))
  have h := trdeg_add_eq ℂ (MvPolynomial ι ℂ)
    (A := FractionRing (MvPolynomial ι ℂ))
  rw [trdeg_eq_zero (R := MvPolynomial ι ℂ)
    (A := FractionRing (MvPolynomial ι ℂ)), add_zero] at h
  rw [← h]
  simp only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype, Cardinal.lift_id]

theorem targetField_trdeg : Algebra.trdeg ℂ K = 16 := by
  rw [(targetPairRationalEquiv ℂ).trdeg_eq, polynomial_fraction_trdeg]
  have hc : Fintype.card (AlgebraicGeometry.Grassmannian.ChartIndex
      (k := 4) (n := 6) ConicFrameCoordinateIndex.pivotEmbedding) = 8 := by
    simpa only [Fintype.card_fin] using
      Fintype.card_congr ConicFrameCoordinateIndex.coordinateEquiv
  have hsum : Fintype.card
      (AlgebraicGeometry.Grassmannian.ChartIndex
          (k := 4) (n := 6) ConicFrameCoordinateIndex.pivotEmbedding ⊕
        AlgebraicGeometry.Grassmannian.ChartIndex
          (k := 4) (n := 6) ConicFrameCoordinateIndex.pivotEmbedding) = 16 := by
    rw [Fintype.card_sum]
    omega
  rw [hsum]
  norm_num

theorem sourceField_trdeg : Algebra.trdeg ℂ L = 16 := by
  rw [(sourcePairRationalEquiv ℂ).trdeg_eq, polynomial_fraction_trdeg]
  norm_num

/-- Both domain and separability hypotheses were proved for these exact
independent coordinate rings; only the actual fibre count is then consumed. -/
theorem pair_field_finite_degree :
    letI := actualFieldAlgebra
    Module.Finite K L ∧ Module.finrank K L = 576 := by
  let := coordinateAlgebra
  have := coordinateTower
  let := coordinateFractionAlgebra
  let := actualFieldAlgebra
  have : @IsScalarTower ℂ K L (inferInstance : Algebra ℂ K).toSMul
      actualFieldAlgebra.toSMul (inferInstance : Algebra ℂ L).toSMul :=
    IsScalarTower.of_algHom (pairFieldEmbedding ℂ)
  have : @IsScalarTower ℂ A L (inferInstance : Algebra ℂ A).toSMul
      coordinateFractionAlgebra.toSMul (inferInstance : Algebra ℂ L).toSMul := IsScalarTower.of_algHom
    ((IsScalarTower.toAlgHom ℂ B L).comp (coordinatePairMap ℂ))
  have : @IsScalarTower A B L coordinateAlgebra.toSMul
      (inferInstance : Algebra B L).toSMul coordinateFractionAlgebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : @IsScalarTower A K L (inferInstance : Algebra A K).toSMul
      actualFieldAlgebra.toSMul coordinateFractionAlgebra.toSMul := by
    apply IsScalarTower.of_algebraMap_eq'
    apply RingHom.ext
    intro a
    exact (pairFieldEmbedding_algebraMap ℂ a).symm
  have : Algebra.IsSeparable K L :=
    GenericEtaleFibreDegree.isSeparable_of_equal_finite_trdeg ℂ K L
      (by rw [targetField_trdeg]; exact Cardinal.ofNat_lt_aleph0)
      (by rw [targetField_trdeg, sourceField_trdeg])
  exact GenericEtaleFibreDegree.finite_and_fraction_finrank_eq_of_nonempty_pointLifts_card
    ℂ A B K L (coordinatePairMap_injective ℂ) 576 (by norm_num)
    ConicFrameTensorPointFiber.card_pointLifts

theorem pair_field_finrank :
    letI := actualFieldAlgebra
    Module.finrank K L = 576 := pair_field_finite_degree.2

theorem pair_field_finite :
    letI := actualFieldAlgebra
    Module.Finite K L := pair_field_finite_degree.1

end M9Native.ConicFramePairDegree
