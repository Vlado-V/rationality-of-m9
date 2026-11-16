module

public import M9StacksIntegration.LagrangianTranslatedDeterminantSections
public import M9StacksIntegration.PrimitiveCoefficientMatrices

/-! The actual translated determinant tuple in the original native
primitive basis, including its multiplication and inverse-dual conventions. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Module Matrix
open scoped BigOperators

universe u

namespace M9Native.LagrangianTranslatedDeterminantCoordinates

open LagrangianTranslatedDeterminantSections LagrangianTransitivity
open LagrangianSigmaInvariance PrimitiveRingMatrices PrimitiveCoefficientMatrices
open MukaiConormalBigCellSections LagrangianMatrixChart
open LagrangianPluckerQuotient LagrangianTranslatedCharts

variable (K : Type u) [Field K] [CharZero K]

theorem transpose_map {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (g : Matrix.symplecticGroup (Fin 3) R) :
    transposeSymplectic S (mapSymplectic R φ g) =
      mapSymplectic R φ (transposeSymplectic R g) := by
  apply Subtype.ext
  rfl

theorem transpose_mul {R : Type u} [CommRing R]
    (g h : Matrix.symplecticGroup (Fin 3) R) :
    transposeSymplectic R (g*h) = transposeSymplectic R h * transposeSymplectic R g := by
  apply Subtype.ext
  exact Matrix.transpose_mul _ _

theorem transpose_one {R : Type u} [CommRing R] :
    transposeSymplectic R (1 : Matrix.symplecticGroup (Fin 3) R) = 1 := by
  apply Subtype.ext
  exact Matrix.transpose_one

theorem transpose_inv {R : Type u} [CommRing R]
    (g : Matrix.symplecticGroup (Fin 3) R) :
    transposeSymplectic R g⁻¹ = (transposeSymplectic R g)⁻¹ := by
  have h : transposeSymplectic R g⁻¹ * transposeSymplectic R g = 1 := by
    rw [← transpose_mul,mul_inv_cancel,transpose_one]
  calc
    _ = transposeSymplectic R g⁻¹ * 1 := (mul_one _).symm
    _ = transposeSymplectic R g⁻¹ *
        (transposeSymplectic R g * (transposeSymplectic R g)⁻¹) := by rw [mul_inv_cancel]
    _ = (transposeSymplectic R g⁻¹ * transposeSymplectic R g) *
        (transposeSymplectic R g)⁻¹ := (mul_assoc _ _ _).symm
    _ = _ := by rw [h,one_mul]

/-- Every positive coefficient uses the actual native primitive basis. -/
def positiveMatrix (g : Matrix.symplecticGroup (Fin 3) K) : Matrix (Fin 14) (Fin 14) K :=
  matrix14 K K (RingHom.id K) (transposeSymplectic K g)

theorem translatedPolynomial_native (g : Matrix.symplecticGroup (Fin 3) K) :
    translatedPolynomial K g =
      (positiveMatrix K g).map (MvPolynomial.C : K →+* MukaiConormalBigCellSections.Ring K) *ᵥ
        sectionPolynomial K := by
  rw [translatedPolynomial_positive,transpose_map]
  have h := matrix14_map K K (RingHom.id K)
    (MvPolynomial.C : K →+* MukaiConormalBigCellSections.Ring K) (transposeSymplectic K g)
  simpa only [RingHom.comp_id,positiveMatrix] using
    congrArg (fun M => M *ᵥ sectionPolynomial K) h

theorem translatedPolynomial_mul (g h : Matrix.symplecticGroup (Fin 3) K) :
    translatedPolynomial K (g*h) =
      (positiveMatrix K h).map (MvPolynomial.C : K →+* MukaiConormalBigCellSections.Ring K) *ᵥ
        translatedPolynomial K g := by
  rw [translatedPolynomial_native,translatedPolynomial_native]
  simp only [positiveMatrix,transpose_mul,matrix14_mul,Matrix.map_mul,Matrix.mulVec_mulVec]

/-- The original native determinant sections in the two actual frames
satisfy the exact positive matrix law over the same actual chart. -/
theorem translatedSections_mul (g h : Matrix.symplecticGroup (Fin 3) K) (j : Fin 14) :
    (show Γ(chart K,⊤) from (translatedDeterminantIso K (g*h)).hom.app ⊤
        (pullbackGlobalSections (translatedBigCell K (g*h)) (determinantLine K)
          (primitiveSections K j))) =
      ∑ k, scalarEquiv K (MvPolynomial.C (positiveMatrix K h j k)) *
        (show Γ(chart K,⊤) from (translatedDeterminantIso K g).hom.app ⊤
          (pullbackGlobalSections (translatedBigCell K g) (determinantLine K)
            (primitiveSections K k))) := by
  simp only [translatedDeterminantIso_coordinate]
  rw [translatedPolynomial_mul]
  simp only [Matrix.mulVec,dotProduct,map_sum,map_mul,Matrix.map_apply]

/-- The actual native action at the inverse matrix is its actual inverse. -/
theorem primitiveAction_inv (g : Matrix.symplecticGroup (Fin 3) K) :
    PrimitiveCoefficientAction.primitiveAction K g⁻¹ =
      (PrimitiveCoefficientAction.primitiveAction K g).symm := by
  apply LinearEquiv.ext
  intro v
  change PrimitiveCoefficientAction.primitiveEquiv K
      ((PrimitiveRingRepresentation.primitiveRepresentation K) g⁻¹
        ((PrimitiveCoefficientAction.primitiveEquiv K).symm v)) =
    PrimitiveCoefficientAction.primitiveEquiv K
      (((PrimitiveRingRepresentation.primitiveRepresentation K) g)⁻¹
        ((PrimitiveCoefficientAction.primitiveEquiv K).symm v))
  rw [map_inv]

/-- The required inverse orientation is the literal inverse dual of
our actual positive primitive action. -/
theorem inverseDual_eq_quotientMap (g : Matrix.symplecticGroup (Fin 3) K) :
    (PrimitiveCoefficientAction.primitiveAction K (transposeSymplectic K g)).symm.dualMap.toLinearMap =
      MukaiPrimitiveQuartic.quotientMap K (matrixSix K g⁻¹).mulVecLin := by
  rw [MukaiPrimitiveQuarticAction.quotientMap_eq_dualMap_transpose,
    transpose_inv,primitiveAction_inv]

end M9Native.LagrangianTranslatedDeterminantCoordinates
