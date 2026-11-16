module

public import M9StacksIntegration.LagrangianDeterminantActionMatrix
public import M9StacksIntegration.LagrangianPrimitiveRowAction
public import M9StacksIntegration.MukaiConormalBigCellSections
public import M9StacksIntegration.LagrangianTranslatedCharts

/-! Actual positive primitive coordinates on the native translated LG
charts. The original determinant sections and the actual line frame are
retained; the transpose action is derived from their quotient rows. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 100000
set_option Elab.async false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Matrix

universe u

namespace M9Native.LagrangianTranslatedDeterminantSections

open LagrangianGrassmannian LagrangianMatrixChart LagrangianPluckerQuotient
open LagrangianSymplecticAction LagrangianTransitivity LagrangianSigmaInvariance
open LagrangianTranslatedCharts LagrangianBigCellQuotient LagrangianPluckerEpimorphism
open LagrangianDeterminantAction LagrangianPrimitiveRowAction LagrangianPullback
open MukaiConormalBigCellSections hiding chart
open AlgebraicGeometry.Grassmannian

variable (K : Type u) [Field K] [CharZero K]
  (g : Matrix.symplecticGroup (Fin 3) K)

def translatedQuotientIso :
    (pullbackPresentation (translatedBigCell K g) (quotientOnLG K)).target ≅
      freeOn (MukaiConormalBigCellSections.chart K) 3 :=
  quotientActionIso K (bigCell K) g ≪≫ bigCellQuotientIso K

def translatedMatrix : Matrix (Fin 3) (Fin 6) (MukaiConormalBigCellSections.Ring K) :=
  graphQuotientMatrix K * matrixSix (MukaiConormalBigCellSections.Ring K) (mapSymplectic K MvPolynomial.C g)

theorem coefficientMap_eq_scalarMap {T : Scheme.{u}} (f : T ⟶ space K) :
    scalarMap K (f ≫ projection K) = LagrangianPlucker.coefficientMap K f := rfl

theorem translatedQuotientIso_matrix :
    Stacks.FreeSheafMatrix.toMatrix
      ((pullbackPresentation (translatedBigCell K g) (quotientOnLG K)).map ≫
        (translatedQuotientIso K g).hom) =
      (translatedMatrix K g).map (scalarEquiv K).toRingHom := by
  have h := LagrangianDeterminantActionMatrix.framed_matrix K (bigCell K) g (bigCellQuotientIso K)
  have hm : Stacks.FreeSheafMatrix.toMatrix
      ((pullbackPresentation (bigCell K) (quotientOnLG K)).map ≫
        (bigCellQuotientIso K).hom) * constantMatrix K (bigCell K ≫ projection K) g =
      (translatedMatrix K g).map (scalarEquiv K).toRingHom := by
    rw [original_bigCell_matrix]
    have hc : scalarMap K (bigCell K ≫ projection K) =
        (scalarEquiv K).toRingHom.comp MvPolynomial.C :=
      (coefficientMap_eq_scalarMap K (bigCell K)).trans (bigCell_coefficientMap K)
    change (graphQuotientMatrix K).map (scalarEquiv K).toRingHom *
      (matrixSix K g).map (scalarMap K (bigCell K ≫ projection K)) = _
    rw [hc]
    simpa only [translatedMatrix,matrixSix_map] using
      LagrangianDeterminantActionMatrix.map_mul_scalar (graphQuotientMatrix K) (matrixSix K g)
        (MvPolynomial.C : K →+* MukaiConormalBigCellSections.Ring K) (scalarEquiv K).toRingHom
  exact h.trans hm

def translatedDeterminantIso :
    (Scheme.Modules.pullback (translatedBigCell K g)).obj (determinantLine K) ≅
      SheafOfModules.unit (MukaiConormalBigCellSections.chart K).ringCatSheaf :=
  determinantTransportIso K (translatedBigCell K g) (translatedQuotientIso K g) ≪≫
    LagrangianAffineDeterminant.affineDeterminantIso (MukaiConormalBigCellSections.chart K)

def translatedPolynomial (j : Fin 14) : MukaiConormalBigCellSections.Ring K :=
  LagrangianRing.rowFourteen (MukaiConormalBigCellSections.Ring K) (MvPolynomial.C : K →+* MukaiConormalBigCellSections.Ring K)
    (translatedMatrix K g) j

/-- The actual acted determinant sections become the actual translated
row polynomials in the constructed native determinant frame. -/
theorem translatedDeterminantIso_coordinate (j : Fin 14) :
    (translatedDeterminantIso K g).hom.app ⊤
      (pullbackGlobalSections (translatedBigCell K g) (determinantLine K) (primitiveSections K j)) =
        scalarEquiv K (translatedPolynomial K g j) := by
  change (LagrangianAffineDeterminant.affineDeterminantIso _).hom.app ⊤
    ((determinantTransportIso K (translatedBigCell K g) (translatedQuotientIso K g)).hom.app ⊤
      (pullbackGlobalSections (translatedBigCell K g) (determinantLine K) (primitiveSections K j))) = _
  rw [determinantTransportIso_primitive,LagrangianAffineDeterminant.affineDeterminantIso_coordinate,
    primitiveSection_freeCoordinates,translatedQuotientIso_matrix]
  have hc : LagrangianPlucker.coefficientMap K (translatedBigCell K g) =
      (scalarEquiv K).toRingHom.comp MvPolynomial.C :=
    (coefficientMap_action K (bigCell K) g).trans (bigCell_coefficientMap K)
  rw [hc]
  exact congrFun (LagrangianPlucker.rowFourteen_map K
    (MvPolynomial.C : K →+* MukaiConormalBigCellSections.Ring K) (scalarEquiv K).toRingHom (translatedMatrix K g)) j

/-- The literal positive primitive action is obtained from the transpose
symplectic exterior matrix, with no coordinate-action premise. -/
theorem translatedPolynomial_positive :
    translatedPolynomial K g =
      PrimitiveRingMatrices.matrix14 (MukaiConormalBigCellSections.Ring K) K MvPolynomial.C
        (transposeSymplectic (MukaiConormalBigCellSections.Ring K) (mapSymplectic K MvPolynomial.C g)) *ᵥ
          sectionPolynomial K := by
  exact rowFourteen_mul_symplectic (MukaiConormalBigCellSections.Ring K) K MvPolynomial.C (graphQuotientMatrix K)
    (by
      intro i j
      simp only [graphQuotientMatrix,LagrangianRing.omega_apply,LagrangianRing.omegaValue,
        LagrangianRing.eIndex,LagrangianRing.fIndex,LagrangianPluckerFirstJet.standard_e,
        LagrangianPluckerFirstJet.standard_f,Finset.sum_sub_distrib]
      simp only [ite_mul,one_mul,zero_mul,mul_ite,mul_one,mul_zero,
        Finset.sum_ite_eq,Finset.mem_univ,ite_true]
      simp only [graphMatrix]
      rw [symmetricIndex_swap j i]
      exact sub_self _)
    (mapSymplectic K MvPolynomial.C g)

end M9Native.LagrangianTranslatedDeterminantSections
