module

public import M9StacksIntegration.LagrangianQuadricChartReindex
public import M9StacksIntegration.MukaiConormalBigCellSections

/-! The exact normalized graph kernel in the original native big-cell
coordinate ring. The actual quotient [I|A] and actual fourteen determinant
sections, including their original finite basis numbering, are retained. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open MvPolynomial Matrix

universe u

namespace M9Native.LagrangianBigCellQuadricCoordinates

open LagrangianQuadricChartAlgebra

variable (K : Type u) [Field K]

abbrev NativeRing := MukaiConormalBigCellSections.Ring K

def nativeAffineEquiv : AffineRing K ≃ₐ[K] NativeRing K :=
  MvPolynomial.renameEquiv K LagrangianMatrixChart.symmetricEntryEquivFinSix

theorem genericMatrix_native : (genericMatrix K).map (nativeAffineEquiv K).toAlgHom =
    MukaiConormalBigCellSections.graphMatrix K := by
  funext i j
  exact MvPolynomial.rename_X _ _

theorem native_graphMatrix_symmetric :
    (MukaiConormalBigCellSections.graphMatrix K).transpose =
      MukaiConormalBigCellSections.graphMatrix K := by
  rw [← genericMatrix_native, ← Matrix.transpose_map, genericMatrix_symmetric]

def blockGraphEvaluation : LagrangianHomogeneousQuadrics.Ring K →ₐ[K] NativeRing K :=
  (nativeAffineEquiv K).toAlgHom.comp
    ((graphMap K).comp (LagrangianQuadricDehomogenization.dehom K))

theorem blockGraphEvaluation_a :
    blockGraphEvaluation K (LagrangianHomogeneousQuadrics.aVariable K) = 1 := by
  change nativeAffineEquiv K (graphMap K
    (LagrangianQuadricDehomogenization.dehom K (LagrangianHomogeneousQuadrics.aVariable K))) = 1
  rw [LagrangianQuadricDehomogenization.dehom_a, map_one, map_one]

theorem blockGraphEvaluation_b :
    blockGraphEvaluation K (LagrangianHomogeneousQuadrics.bVariable K) =
      (MukaiConormalBigCellSections.graphMatrix K).det := by
  change nativeAffineEquiv K (graphMap K
    (LagrangianQuadricDehomogenization.dehom K (LagrangianHomogeneousQuadrics.bVariable K))) = _
  rw [LagrangianQuadricDehomogenization.dehom_b, graphMap_bVariable]
  have h := (nativeAffineEquiv K).toAlgHom.map_det (genericMatrix K)
  simp only [AlgHom.mapMatrix_apply] at h
  rw [genericMatrix_native] at h
  exact h

theorem blockGraphEvaluation_pMatrix :
    (LagrangianHomogeneousQuadrics.pMatrix K).map (blockGraphEvaluation K) =
      MukaiConormalBigCellSections.graphMatrix K := by
  change (((LagrangianHomogeneousQuadrics.pMatrix K).map
      (LagrangianQuadricDehomogenization.dehom K)).map (graphMap K)).map
        (nativeAffineEquiv K).toAlgHom = _
  rw [LagrangianQuadricDehomogenization.dehom_pMatrix, graphMap_pMatrix, genericMatrix_native]

theorem blockGraphEvaluation_qMatrix :
    (LagrangianHomogeneousQuadrics.qMatrix K).map (blockGraphEvaluation K) =
      (MukaiConormalBigCellSections.graphMatrix K).adjugate := by
  change (((LagrangianHomogeneousQuadrics.qMatrix K).map
      (LagrangianQuadricDehomogenization.dehom K)).map (graphMap K)).map
        (nativeAffineEquiv K).toAlgHom = _
  rw [LagrangianQuadricDehomogenization.dehom_qMatrix, graphMap_qMatrix]
  have h := (nativeAffineEquiv K).toAlgHom.map_adjugate (genericMatrix K)
  simp only [AlgHom.mapMatrix_apply] at h
  rw [genericMatrix_native] at h
  exact h

theorem blockGraphEvaluation_p_upper (ij : SymIndex.{u}) :
    blockGraphEvaluation K (X (Sum.inr (Sum.inr (Sum.inl ij)))) =
      MukaiConormalBigCellSections.graphMatrix K ij.down.val.1 ij.down.val.2 := by
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) (NativeRing K) => A ij.down.val.1 ij.down.val.2)
    (blockGraphEvaluation_pMatrix K)
  have hi : LagrangianMatrixChart.symmetricIndex (ij.down.val.1, ij.down.val.2) = ij.down :=
    LagrangianMatrixChart.symmetricIndex_of_le ij.down
  simp only [Matrix.map_apply, LagrangianHomogeneousQuadrics.pMatrix, hi, ULift.up_down] at h
  exact h

theorem blockGraphEvaluation_q_upper (ij : SymIndex.{u}) :
    blockGraphEvaluation K (X (Sum.inr (Sum.inl ij))) =
      (MukaiConormalBigCellSections.graphMatrix K).adjugate ij.down.val.1 ij.down.val.2 := by
  have h := congrArg (fun A : Matrix (Fin 3) (Fin 3) (NativeRing K) => A ij.down.val.1 ij.down.val.2)
    (blockGraphEvaluation_qMatrix K)
  have hi : LagrangianMatrixChart.symmetricIndex (ij.down.val.1, ij.down.val.2) = ij.down :=
    LagrangianMatrixChart.symmetricIndex_of_le ij.down
  simp only [Matrix.map_apply, LagrangianHomogeneousQuadrics.qMatrix, hi, ULift.up_down] at h
  exact h

/-- Each original determinant-section polynomial is exactly its
normalized graph value in the original native finite basis. -/
theorem blockGraphEvaluation_X (i : LagrangianHomogeneousQuadrics.CoordinateIndex.{u}) :
    blockGraphEvaluation K (X i) = MukaiConormalBigCellSections.sectionPolynomial K
      (LagrangianPrimitiveQuadrics.coordinateIndexEquiv i) := by
  have he := LagrangianRingCoordinateEntries.rowFourteen_entry
    (MvPolynomial.C : K →+* NativeRing K) (MukaiConormalBigCellSections.graphQuotientMatrix K)
    (LagrangianPrimitiveQuadrics.blockIndexEquiv i)
  refine (show blockGraphEvaluation K (X i) = LagrangianRingCoordinateEntries.extraction (NativeRing K)
    (LagrangianPrimitiveQuadrics.blockIndexEquiv i)
    (LagrangianRing.rowPlucker (NativeRing K) (MukaiConormalBigCellSections.graphQuotientMatrix K)) from ?_).trans he.symm
  cases i with
  | inl i =>
    change blockGraphEvaluation K (LagrangianHomogeneousQuadrics.aVariable K) =
      LagrangianPluckerFirstJet.aCoordinate _ (LagrangianRing.rowPlucker _
        (LagrangianPluckerFirstJet.standard _ (MukaiConormalBigCellSections.graphMatrix K)))
    rw [blockGraphEvaluation_a, LagrangianPluckerFirstJet.aCoordinate_standard]
  | inr i =>
    cases i with
    | inl ij =>
      change blockGraphEvaluation K (X (Sum.inr (Sum.inl ij))) =
        LagrangianPluckerFirstJet.qCoordinate _ ij.down.val.1 ij.down.val.2
          (LagrangianRing.rowPlucker _
            (LagrangianPluckerFirstJet.standard _ (MukaiConormalBigCellSections.graphMatrix K)))
      rw [blockGraphEvaluation_q_upper, LagrangianPluckerFirstJet.qCoordinate_standard]
      have hs : (MukaiConormalBigCellSections.graphMatrix K).adjugate.transpose =
          (MukaiConormalBigCellSections.graphMatrix K).adjugate := by
        rw [Matrix.adjugate_transpose, native_graphMatrix_symmetric]
      exact (congrFun (congrFun hs ij.down.val.1) ij.down.val.2).symm
    | inr i =>
      cases i with
      | inl ij =>
        change blockGraphEvaluation K (X (Sum.inr (Sum.inr (Sum.inl ij)))) =
          LagrangianPluckerFirstJet.pCoordinate _ ij.down.val.1 ij.down.val.2
            (LagrangianRing.rowPlucker _
              (LagrangianPluckerFirstJet.standard _ (MukaiConormalBigCellSections.graphMatrix K)))
        rw [blockGraphEvaluation_p_upper, LagrangianPluckerFirstJet.pCoordinate_standard]
        exact (congrFun (congrFun (native_graphMatrix_symmetric K) ij.down.val.1) ij.down.val.2).symm
      | inr i =>
        change blockGraphEvaluation K (LagrangianHomogeneousQuadrics.bVariable K) =
          LagrangianPluckerFirstJet.bCoordinate _ (LagrangianRing.rowPlucker _
            (LagrangianPluckerFirstJet.standard _ (MukaiConormalBigCellSections.graphMatrix K)))
        rw [blockGraphEvaluation_b, LagrangianPluckerFirstJet.bCoordinate_standard]

def nativeChartGraphMap : MvPolynomial (Fin 13) K →ₐ[K] NativeRing K :=
  (nativeAffineEquiv K).toAlgHom.comp (LagrangianQuadricChartReindex.nativeGraphMap K)

theorem nativeChartGraphMap_surjective : Function.Surjective (nativeChartGraphMap K) := by
  intro x
  let y := (nativeAffineEquiv K).symm x
  refine ⟨(LagrangianQuadricChartReindex.chartRingEquiv K).symm
    (MvPolynomial.rename Sum.inr y), ?_⟩
  change nativeAffineEquiv K (graphMap K
    (LagrangianQuadricChartReindex.chartRingEquiv K
      ((LagrangianQuadricChartReindex.chartRingEquiv K).symm
        (MvPolynomial.rename Sum.inr y)))) = x
  rw [AlgEquiv.apply_symm_apply]
  have h := AlgHom.congr_fun (PolynomialGraphKernel.graphEvaluation_comp_rename K
    ExtraIndex.{u} SymIndex.{u} (extraPolynomials K)) y
  change graphMap K (MvPolynomial.rename Sum.inr y) = y at h
  rw [h]
  exact (nativeAffineEquiv K).apply_symm_apply x

/-- The entire original normalized polynomial map agrees with the
literal native determinant-section tuple. -/
theorem nativeChartGraphMap_comp_dehom : (nativeChartGraphMap K).toRingHom.comp
    (Stacks.ProjectiveChart.dehomCoeff K LagrangianQuadricChartReindex.aIndex) =
      MvPolynomial.eval₂Hom MvPolynomial.C (MukaiConormalBigCellSections.sectionPolynomial K) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [nativeChartGraphMap, LagrangianQuadricChartReindex.nativeGraphMap,
      LagrangianQuadricChartReindex.chartRingEquiv, nativeAffineEquiv,
      Stacks.ProjectiveChart.dehomCoeff_eq_aeval]
  · intro j
    obtain ⟨i, rfl⟩ := LagrangianPrimitiveQuadrics.coordinateIndexEquiv.surjective j
    have h := congrArg (fun p : LocalRing K => nativeAffineEquiv K (graphMap K p))
      (RingHom.congr_fun (LagrangianQuadricChartReindex.nativeDehom_comp_rename K) (X i))
    simp only [RingHom.comp_apply] at h
    have hx : MvPolynomial.rename LagrangianPrimitiveQuadrics.coordinateIndexEquiv (X i :
        LagrangianHomogeneousQuadrics.Ring K) = X (LagrangianPrimitiveQuadrics.coordinateIndexEquiv i) :=
      MvPolynomial.rename_X _ _
    change nativeAffineEquiv K (graphMap K (LagrangianQuadricChartReindex.nativeDehom K
      (MvPolynomial.rename LagrangianPrimitiveQuadrics.coordinateIndexEquiv (X i)))) =
        blockGraphEvaluation K (X i) at h
    rw [hx] at h
    rw [MvPolynomial.eval₂Hom_X']
    exact h.trans (blockGraphEvaluation_X K i)

theorem ker_nativeChartGraphMap : RingHom.ker (nativeChartGraphMap K).toRingHom =
    LagrangianQuadricChartReindex.nativeChartIdeal K := by
  ext p
  change nativeAffineEquiv K (LagrangianQuadricChartReindex.nativeGraphMap K p) = 0 ↔ _
  rw [map_eq_zero_iff _ (nativeAffineEquiv K).injective]
  exact Iff.of_eq (congrArg (fun I : Ideal (MvPolynomial (Fin 13) K) => p ∈ I)
    (LagrangianQuadricChartReindex.ker_nativeGraphMap K))

end M9Native.LagrangianBigCellQuadricCoordinates
