module

public import M9StacksIntegration.MukaiConormalOriginCoordinates
public import M9StacksIntegration.LagrangianBigCellMatrixEntries
public import M9StacksIntegration.LagrangianPluckerEpimorphism
public import M9StacksIntegration.LagrangianAffineDeterminant

/-! The actual native determinant sections on the original LG big cell,
retaining the genuine quotient frame and original polynomial numbering. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Matrix

universe u

namespace M9Native.MukaiConormalBigCellSections

open LagrangianGrassmannian LagrangianMatrixChart LagrangianBigCellQuotient
open LagrangianPluckerQuotient LagrangianPluckerFirstJet
open AlgebraicGeometry.Grassmannian

variable (K : Type u) [Field K]

abbrev Ring := MvPolynomial (Fin 6) K
abbrev chart : Scheme.{u} := Spec (.of (Ring K))

def scalarEquiv : Ring K ≃+* Γ(chart K,⊤) :=
  (Scheme.ΓSpecIso (.of (Ring K))).symm.commRingCatIsoToRingEquiv

def graphMatrix : Matrix (Fin 3) (Fin 3) (Ring K) :=
  fun i j => MvPolynomial.X (symmetricEntryEquivFinSix (ULift.up.{u} (symmetricIndex (i,j))))

def graphQuotientMatrix : Matrix (Fin 3) (Fin 6) (Ring K) := standard (Ring K) (graphMatrix K)

theorem original_bigCell_matrix :
    Stacks.FreeSheafMatrix.toMatrix (X := chart K) (a := 6) (b := 3)
      ((pullbackPresentation (bigCell K) (quotientOnLG K)).map ≫ (bigCellQuotientIso K).hom) =
        (graphQuotientMatrix K).map (scalarEquiv K).toRingHom := by
  ext i j
  refine Fin.addCases (m := 3) (n := 3) (fun j => ?_) (fun j => ?_) j
  · rw [bigCellQuotient_first]
    simp [graphQuotientMatrix, standard_e]
  · rw [bigCellQuotient_last]
    change (scalarEquiv K) (MvPolynomial.X
        (symmetricEntryEquivFinSix (ULift.up.{u} (symmetricIndex (i,j))))) =
      (scalarEquiv K) (standard (Ring K) (graphMatrix K) i (Fin.natAdd 3 j))
    rw [standard_f]
    rfl

theorem bigCell_coefficientMap :
    LagrangianPlucker.coefficientMap K (bigCell K) =
      (scalarEquiv K).toRingHom.comp MvPolynomial.C := by
  unfold LagrangianPlucker.coefficientMap
  rw [bigCell_projection, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

def sectionPolynomial (j : Fin 14) : Ring K :=
  LagrangianRing.rowFourteen (Ring K) (MvPolynomial.C : K →+* Ring K)
    (graphQuotientMatrix K) j

/-- The actual original determinant-line trivialization coming from the
actual native normalized quotient, with no chosen scalar identification. -/
def determinantIso :
    (Scheme.Modules.pullback (bigCell K)).obj (determinantLine K) ≅
      SheafOfModules.unit (chart K).ringCatSheaf :=
  LagrangianPluckerEpimorphism.determinantTransportIso K (bigCell K) (bigCellQuotientIso K) ≪≫
    LagrangianAffineDeterminant.affineDeterminantIso (chart K)

/-- All fourteen original native determinant sections become the actual
fourteen projected quotient-minor polynomials in this genuine frame. -/
theorem determinantIso_coordinate (j : Fin 14) :
    (determinantIso K).hom.app ⊤
        (pullbackGlobalSections (bigCell K) (determinantLine K) (primitiveSections K j)) =
      scalarEquiv K (sectionPolynomial K j) := by
  change (LagrangianAffineDeterminant.affineDeterminantIso (chart K)).hom.app ⊤
    ((LagrangianPluckerEpimorphism.determinantTransportIso K (bigCell K)
      (bigCellQuotientIso K)).hom.app ⊤
      (pullbackGlobalSections (bigCell K) (determinantLine K) (primitiveSections K j))) = _
  rw [LagrangianPluckerEpimorphism.determinantTransportIso_primitive,
    LagrangianAffineDeterminant.affineDeterminantIso_coordinate,
    primitiveSection_freeCoordinates, original_bigCell_matrix, bigCell_coefficientMap]
  exact congrFun (LagrangianPlucker.rowFourteen_map K
    (MvPolynomial.C : K →+* Ring K) (scalarEquiv K).toRingHom (graphQuotientMatrix K)) j

end M9Native.MukaiConormalBigCellSections
