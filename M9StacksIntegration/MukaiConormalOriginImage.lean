module

public import M9StacksIntegration.MukaiConormalChartImage
public import M9StacksIntegration.MukaiConormalPolynomialTangent

/-! The actual native conormal Euler image at the standard field point
is the literal origin conormal space. Native universal differentials are
compared with the original dual-number jets, with no image premise. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

namespace M9Native.MukaiConormalOriginImage

open LagrangianGrassmannian LagrangianMatrixChart LagrangianPluckerQuotient
open MukaiConormalBigCellSections MukaiConormalBigCellFirstJet MukaiConormalOriginFrame
open MukaiConormalOriginCoordinates

variable (K : Type u) [Field K] [CharZero K]

abbrev originalTuple := MukaiConormalChartFrame.sectionTuple K (bigCell K)
  (MukaiConormalBigCellSections.determinantIso K)

omit [CharZero K] in
theorem originalTuple_coordinate (j : Fin 14) :
    originalTuple K j = MukaiConormalBigCellSections.scalarEquiv K (sectionPolynomial K j) :=
  determinantIso_coordinate K j

theorem value_coordinate (j : Fin 14) :
    MukaiConormalChartJets.value K (zeroPoint K) (originalTuple K j) =
      (LagrangianPluckerLinear.primitiveBasis14 K).equivFun
        (MukaiConormalOrigin.originPoint K) j := by
  change (Scheme.ΓSpecIso (.of K)).hom ((zeroPoint K).appTop (originalTuple K j)) = _
  rw [originalTuple_coordinate, zeroPoint_scalar]
  change (Scheme.ΓSpecIso (.of K)).hom ((Scheme.ΓSpecIso (.of K)).inv
    (originEval K (sectionPolynomial K j))) = _
  rw [(Scheme.ΓSpecIso (.of K)).inv_hom_id_apply, sectionPolynomial_origin_primitive]

theorem derivative_coordinate (B : LagrangianField.Symmetric3 K) (j : Fin 14) :
    MukaiConormalPolynomialTangent.jetValue K B
      (MukaiConormalChartJets.derivative K (zeroPoint K) (originalTuple K j)) =
        (LagrangianPluckerLinear.primitiveBasis14 K).equivFun
          (MukaiConormalOrigin.originJet K B) j := by
  change MukaiConormalPolynomialTangent.jetValue K B
    (pullbackGlobalSections (zeroPoint K) (MukaiConormalPolynomialTangent.Cotangent K)
      ((Scheme.Hom.universalRelativeDerivation (LagrangianChartCotangent.chartProjection K)).d
        (originalTuple K j))) = _
  rw [originalTuple_coordinate, MukaiConormalPolynomialTangent.jetValue_d,
    sectionPolynomial_firstJet_primitive]

theorem valueMap_eq (ell : Module.Dual K (LagrangianField.Primitive K)) :
    MukaiConormalChartJets.valueMap K (zeroPoint K) (originalTuple K) ell =
      ell (MukaiConormalOrigin.originPoint K) := by
  change (∑ j : Fin 14, ell (LagrangianPluckerLinear.primitiveBasis14 K j) *
    MukaiConormalChartJets.value K (zeroPoint K) (originalTuple K j)) = _
  simp_rw [value_coordinate]
  simpa only [LinearEquiv.symm_apply_apply, formsCoordinates_apply] using
    (formsCoordinates_symm_apply K (formsCoordinates K ell)
      (MukaiConormalOrigin.originPoint K)).symm

theorem derivativeMap_eq (ell : Module.Dual K (LagrangianField.Primitive K))
    (B : LagrangianField.Symmetric3 K) :
    MukaiConormalPolynomialTangent.jetValue K B
      (MukaiConormalChartJets.derivativeMap K (zeroPoint K) (originalTuple K) ell) =
        ell (MukaiConormalOrigin.originJet K B) := by
  change MukaiConormalPolynomialTangent.jetValue K B
    (∑ j : Fin 14, ell (LagrangianPluckerLinear.primitiveBasis14 K j) •
      MukaiConormalChartJets.derivative K (zeroPoint K) (originalTuple K j)) = _
  simp only [map_sum, map_smul, RingHom.id_apply, smul_eq_mul, derivative_coordinate]
  simpa only [LinearEquiv.symm_apply_apply, formsCoordinates_apply] using
    (formsCoordinates_symm_apply K (formsCoordinates K ell)
      (MukaiConormalOrigin.originJet K B)).symm

theorem chartJet_kernel_le_originConormal :
    LinearMap.ker (MukaiConormalChartJets.firstJetMap K (zeroPoint K) (originalTuple K)) ≤
      MukaiConormalOrigin.originConormal K := by
  intro ell h
  change MukaiConormalChartJets.firstJetMap K (zeroPoint K) (originalTuple K) ell = 0 at h
  have hv : MukaiConormalChartJets.valueMap K (zeroPoint K) (originalTuple K) ell = 0 :=
    congrArg Prod.fst h
  have hd : MukaiConormalChartJets.derivativeMap K (zeroPoint K) (originalTuple K) ell = 0 :=
    congrArg Prod.snd h
  change MukaiConormalOrigin.firstJetMap K ell = 0
  apply Prod.ext
  · change ell (MukaiConormalOrigin.originPoint K) = 0
    exact (valueMap_eq K ell).symm.trans hv
  · ext B
    change ell (MukaiConormalOrigin.originJet K B) = 0
    have hB := congrArg (MukaiConormalPolynomialTangent.jetValue K B) hd
    simpa only [derivativeMap_eq, map_zero] using hB

variable [IsAlgClosed K]

/-- The original categorical conormal, original Euler twisting and
original native field coordinates have exactly the standard conormal image. -/
theorem range_formsMap_origin :
    LinearMap.range (MukaiConormalFieldCoordinates.formsMap K (origin K)) =
      MukaiConormalOrigin.originConormal K := by
  have hf : bigCell K ≫ projection K = MukaiConormalChartJets.chartProjection K :=
    bigCell_projection K
  have hz : zeroPoint K ≫ MukaiConormalChartJets.chartProjection K = 𝟙 (Spec (.of K)) := by
    rw [← hf, ← Category.assoc]
    exact origin_over_base K
  have hjet := MukaiConormalChartImage.range_formsMap_eq_ker_firstJetMap K (bigCell K)
    hf (zeroPoint K) hz (MukaiConormalBigCellSections.determinantIso K)
  have hle : LinearMap.range (MukaiConormalFieldCoordinates.formsMap K (origin K)) ≤
      MukaiConormalOrigin.originConormal K := by
    rw [show LinearMap.range (MukaiConormalFieldCoordinates.formsMap K (origin K)) =
      LinearMap.ker (MukaiConormalChartJets.firstJetMap K (zeroPoint K) (originalTuple K)) from hjet]
    exact chartJet_kernel_le_originConormal K
  exact Submodule.eq_of_le_of_finrank_eq hle
    ((MukaiConormalFieldCoordinates.finrank_range_formsMap K (origin K)).trans
      (MukaiConormalOrigin.finrank_originConormal K).symm)

end M9Native.MukaiConormalOriginImage
