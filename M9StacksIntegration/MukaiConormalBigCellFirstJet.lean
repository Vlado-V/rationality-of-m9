module

public import M9StacksIntegration.MukaiConormalBigCellSections
public import M9StacksIntegration.MukaiConormalRowCoordinates

/-! Value and genuine dual-number first jets of all original native
primitive determinant sections on the actual LG big cell. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Module Matrix

universe u

namespace M9Native.MukaiConormalBigCellFirstJet

open MukaiConormalBigCellSections MukaiConormalRowCoordinates
open MukaiConormalOriginCoordinates LagrangianPluckerFirstJet LagrangianMatrixChart

variable (K : Type u) [Field K]

abbrev PolynomialRing := MukaiConormalBigCellSections.Ring K

def originEval : PolynomialRing K →ₐ[K] K := MvPolynomial.aeval (fun _ : Fin 6 => 0)

def tangentEval (B : LagrangianField.Symmetric3 K) : PolynomialRing K →ₐ[K] DualNumber K :=
  MvPolynomial.aeval (fun i : Fin 6 =>
    (0, B.val (symmetricEntryEquivFinSix.{u}.symm i).down.val.1
      (symmetricEntryEquivFinSix.{u}.symm i).down.val.2))

theorem standard_map {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (A : Matrix (Fin 3) (Fin 3) R) :
    (standard R A).map φ = standard S (A.map φ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [standard]

theorem graphMatrix_origin : (graphMatrix K).map (originEval K).toRingHom = 0 := by
  ext i j
  simp [graphMatrix, originEval]

theorem graphMatrix_tangent (B : LagrangianField.Symmetric3 K) :
    (graphMatrix K).map (tangentEval K B).toRingHom =
      LagrangianInfinitesimal.firstOrderMatrix K 0 B.val := by
  apply Matrix.ext
  intro i j
  change tangentEval K B (MvPolynomial.X
    (symmetricEntryEquivFinSix (ULift.up.{u} (symmetricIndex (i,j))))) = _
  rw [tangentEval, MvPolynomial.aeval_X, Equiv.symm_apply_apply]
  apply TrivSqZeroExt.ext
  · rfl
  · change B.val (symmetricIndex (i,j)).val.1 (symmetricIndex (i,j)).val.2 = B.val i j
    by_cases h : i ≤ j
    · simp [symmetricIndex, h]
    · simpa [symmetricIndex, h] using congrFun (congrFun B.property i) j

theorem graphQuotient_origin :
    (graphQuotientMatrix K).map (originEval K).toRingHom = standard K 0 := by
  rw [graphQuotientMatrix, standard_map, graphMatrix_origin]

theorem graphQuotient_tangent (B : LagrangianField.Symmetric3 K) :
    (graphQuotientMatrix K).map (tangentEval K B).toRingHom =
      standard (DualNumber K) (LagrangianInfinitesimal.firstOrderMatrix K 0 B.val) := by
  rw [graphQuotientMatrix, standard_map, graphMatrix_tangent]

theorem sectionPolynomial_pivot : sectionPolynomial K originPivot = 1 :=
  rowFourteen_standard_pivot K (MvPolynomial.C : K →+* PolynomialRing K) (graphMatrix K)

theorem sectionPolynomial_tangentEval (B : LagrangianField.Symmetric3 K) (j : Fin 14) :
    tangentEval K B (sectionPolynomial K j) =
      LagrangianRing.rowFourteen (DualNumber K) (algebraMap K (DualNumber K))
        (standard (DualNumber K) (LagrangianInfinitesimal.firstOrderMatrix K 0 B.val)) j := by
  have hc : (tangentEval K B).toRingHom.comp (MvPolynomial.C : K →+* PolynomialRing K) =
      algebraMap K (DualNumber K) := by
    apply RingHom.ext
    intro a
    exact (tangentEval K B).commutes a
  have h := congrFun (LagrangianPlucker.rowFourteen_map K
    (MvPolynomial.C : K →+* PolynomialRing K) (tangentEval K B).toRingHom (graphQuotientMatrix K)) j
  rw [hc, graphQuotient_tangent] at h
  exact h.symm

/-- Every true first coefficient is the corresponding native `p`-jet
coefficient, in the original fourteen-coordinate basis. -/
theorem sectionPolynomial_firstJet (B : LagrangianField.Symmetric3 K) (j : Fin 14) :
    (tangentEval K B (sectionPolynomial K j)).snd =
      (LagrangianField.coordinateBasis14 K).equivFun (0,0,B,0) j := by
  rw [sectionPolynomial_tangentEval]
  exact rowFourteen_standard_firstJet K B j

theorem sectionPolynomial_origin (j : Fin 14) :
    originEval K (sectionPolynomial K j) =
      (LagrangianField.coordinateBasis14 K).equivFun (1,0,0,0) j := by
  have hc : (originEval K).toRingHom.comp (MvPolynomial.C : K →+* PolynomialRing K) = RingHom.id K := by
    ext a
    exact (originEval K).commutes a
  have h := congrFun (LagrangianPlucker.rowFourteen_map K
    (MvPolynomial.C : K →+* PolynomialRing K) (originEval K).toRingHom (graphQuotientMatrix K)) j
  rw [hc, graphQuotient_origin, LagrangianRing.rowFourteen_id_eq_field] at h
  have hr : LagrangianField.rowPlucker K (standard K 0) =
      LagrangianRing.rowPlucker K (standard K 0) := by
    unfold LagrangianField.rowPlucker LagrangianField.wedge3 LagrangianRing.rowPlucker
    congr 1
  have hp : LagrangianField.coordinateProjection K
      (LagrangianRing.rowPlucker K (standard K 0)) = (1,0,0,0) := by
    refine (coordinateProjection_standard K
      (0 : LagrangianInfinitesimal.symmetricMatrices K)).trans ?_
    apply Prod.ext
    · rfl
    apply Prod.ext
    · apply Subtype.ext
      ext i k
      simp [graphPoint]
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · simp [graphPoint]
  rw [LagrangianField.rowFourteen, hr, hp] at h
  exact h.symm

variable [CharZero K]

theorem sectionPolynomial_firstJet_primitive (B : LagrangianField.Symmetric3 K) (j : Fin 14) :
    (tangentEval K B (sectionPolynomial K j)).snd =
      (LagrangianPluckerLinear.primitiveBasis14 K).equivFun (MukaiConormalOrigin.originJet K B) j := by
  rw [sectionPolynomial_firstJet K B j]
  simp [LagrangianPluckerLinear.primitiveBasis14, Module.Basis.equivFun_apply,
    MukaiConormalOrigin.originJet, MukaiConormalOrigin.jetCoordinates]

theorem sectionPolynomial_origin_primitive (j : Fin 14) :
    originEval K (sectionPolynomial K j) =
      (LagrangianPluckerLinear.primitiveBasis14 K).equivFun (MukaiConormalOrigin.originPoint K) j := by
  rw [sectionPolynomial_origin K j]
  simp [LagrangianPluckerLinear.primitiveBasis14, Module.Basis.equivFun_apply,
    MukaiConormalOrigin.originPoint]

end M9Native.MukaiConormalBigCellFirstJet
