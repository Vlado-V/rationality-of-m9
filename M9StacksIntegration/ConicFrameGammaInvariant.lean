module

public import M9StacksIntegration.ConicFrameRationalGamma
public import M9StacksIntegration.ConicFrameSourceMatrix

/-! The literal conic quotient coordinates are invariant under the actual
right tetrahedral action. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace M9Native.ConicFrameGammaInvariant

open ConicFrame ConicFrameProjective ConicFrameCoordinates ConicFrameCoordinateIndex
open ConicFrameSourceAlgebra ConicFrameSourceMatrix ConicFrameGammaCongruence
open ConicFrameRationalGamma QuotientMatrixKernels

theorem genericFrame_firstRow (j : Fin 3) : genericFrame 0 j ≠ 0 := by
  have hinj := IsFractionRing.injective P L
  fin_cases j
  · simp [genericFrame,normalizedFrame]
  · exact fun h => MvPolynomial.X_ne_zero 0 (hinj (by simpa [genericFrame,normalizedFrame] using h))
  · exact fun h => MvPolynomial.X_ne_zero 1 (hinj (by simpa [genericFrame,normalizedFrame] using h))

def rightFrame (g : Gamma) : Mat3 L := genericFrame * (M9.TetrahedralGroup.matrix g).map (algebraMap ℂ L)

theorem rightFrame_firstRow (g : Gamma) (j : Fin 3) : rightFrame g 0 j ≠ 0 := by
  obtain ⟨σ,ε,hg⟩ := M9.TetrahedralGroup.matrix_isSignedPermutation g
  have hg' : (M9.TetrahedralGroup.matrix g).map (algebraMap ℂ L) =
      M9.TetrahedralGroup.signedMatrix L σ ε := by
    rw [hg]
    ext i k
    by_cases hk : k = σ i <;> cases hε : ε i <;>
      simp [M9.TetrahedralGroup.signedMatrix,hk,hε]
  have he : rightFrame g 0 j = genericFrame 0 (σ.symm j) *
      (if ε (σ.symm j) then -1 else 1) := by
    rw [rightFrame,hg',Matrix.mul_apply,Finset.sum_eq_single (σ.symm j)]
    · simp [M9.TetrahedralGroup.signedMatrix]
    · intro i _ hi
      have hne : j ≠ σ i := by
        intro hji
        exact hi (σ.injective (hji.symm.trans (σ.apply_symm_apply j).symm))
      simp [M9.TetrahedralGroup.signedMatrix,hne]
    · simp
  rw [he]
  apply mul_ne_zero (genericFrame_firstRow _)
  cases ε (σ.symm j) <;> norm_num

theorem rightFrame_map (g : Gamma) :
    ((normalizedFrame ℂ) * (M9.TetrahedralGroup.matrix g).map MvPolynomial.C).map
        (algebraMap P L) = rightFrame g := by
  rw [Matrix.map_mul,Matrix.map_map]
  rfl

theorem rationalRepresentation_X_rightFrame (g : Gamma) (a : Fin 8) :
    rationalRepresentation g (algebraMap P L (MvPolynomial.X a)) =
      (rightFrame g 0 0)⁻¹ * rightFrame g
        (M9.ProjectiveFunctionField.matrixIndexEquiv.symm (finSuccAboveEquiv 0 a)).1
        (M9.ProjectiveFunctionField.matrixIndexEquiv.symm (finSuccAboveEquiv 0 a)).2 := by
  rw [rationalRepresentation_X,div_eq_inv_mul]
  have he (i j : Fin 3) :
      algebraMap P L
        (((normalizedFrame ℂ) *
          (M9.TetrahedralGroup.matrix g).map (MvPolynomial.C : ℂ →+* P)) i j) =
      rightFrame g i j := congrFun (congrFun (rightFrame_map g) i) j
  rw [he,he]

theorem genericFrame_image (g : Gamma) :
    genericFrame.map (rationalRepresentation g).toRingHom =
      (rightFrame g 0 0)⁻¹ • rightFrame g := by
  ext i j
  have h00 := rightFrame_firstRow g 0
  change rationalRepresentation g (genericFrame i j) = (rightFrame g 0 0)⁻¹ * rightFrame g i j
  fin_cases i <;> fin_cases j
  · simpa [genericFrame,normalizedFrame] using (inv_mul_cancel₀ h00).symm
  · exact rationalRepresentation_X_rightFrame g 0
  · exact rationalRepresentation_X_rightFrame g 1
  · exact rationalRepresentation_X_rightFrame g 2
  · exact rationalRepresentation_X_rightFrame g 3
  · exact rationalRepresentation_X_rightFrame g 4
  · exact rationalRepresentation_X_rightFrame g 5
  · exact rationalRepresentation_X_rightFrame g 6
  · exact rationalRepresentation_X_rightFrame g 7

theorem genericPivot_unit :
    IsUnit ((quotientMatrix genericFrame).submatrix id pivotEmbedding).det := by
  have hd : algebraMap P L (denominator ℂ) ≠ 0 :=
    by simpa only [map_zero] using (IsFractionRing.injective P L).ne (denominator_ne_zero ℂ)
  apply isUnit_iff_ne_zero.mpr
  change ((quotientMatrix ((normalizedFrame ℂ).map (algebraMap P L))).submatrix id pivotEmbedding).det ≠ 0
  rw [← quotientMatrix_map,Matrix.submatrix_map,← RingHom.mapMatrix_apply,← RingHom.map_det]
  exact hd

theorem normalize_generic_image (g : Gamma) :
    normalize (quotientMatrix (genericFrame.map (rationalRepresentation g).toRingHom)) pivotEmbedding =
      normalize (quotientMatrix genericFrame) pivotEmbedding := by
  let A : Matrix (Fin 2) (Fin 2) L :=
    (rightFrame g 0 0)⁻¹ ^ 4 • (gammaFactor g).map (algebraMap ℂ L)
  have hA : IsUnit A.det := by
    dsimp only [A]
    rw [Matrix.det_smul,← RingHom.mapMatrix_apply,← RingHom.map_det]
    exact (isUnit_iff_ne_zero.mpr (pow_ne_zero _
      (pow_ne_zero _ (inv_ne_zero (rightFrame_firstRow g 0))))).mul
      ((gammaFactor_det_unit g).map (algebraMap ℂ L))
  have hq : quotientMatrix (genericFrame.map (rationalRepresentation g).toRingHom) =
      A * quotientMatrix genericFrame := by
    rw [genericFrame_image,quotientMatrix_smul]
    change (rightFrame g 0 0)⁻¹ ^ 4 •
      quotientMatrix (genericFrame * (M9.TetrahedralGroup.matrix g).map (algebraMap ℂ L)) = _
    rw [quotientMatrix_mul_gamma,Matrix.smul_mul]
  rw [hq]
  exact normalize_mul_left A _ _ hA genericPivot_unit

theorem genericNormalization_formula :
    normalize (quotientMatrix genericFrame) pivotEmbedding =
      (algebraMap P L (denominator ℂ))⁻¹ • (numeratorMatrix ℂ).map (algebraMap P L) := by
  rw [QuotientMatrixKernels.normalize,genericFrame,← quotientMatrix_map,Matrix.submatrix_map]
  change (((pivot ℂ).map (algebraMap P L))⁻¹) *
      ((quotientMatrix (normalizedFrame ℂ)).map (algebraMap P L)) = _
  have hd : ((pivot ℂ).map (algebraMap P L)).det = algebraMap P L (denominator ℂ) := by
    rw [← RingHom.mapMatrix_apply,← RingHom.map_det]
    rfl
  have ha : ((pivot ℂ).map (algebraMap P L)).adjugate =
      (pivot ℂ).adjugate.map (algebraMap P L) := by
    simpa only [RingHom.mapMatrix_apply] using ((algebraMap P L).map_adjugate (pivot ℂ)).symm
  rw [Matrix.inv_def,hd,Ring.inverse_eq_inv,Matrix.smul_mul,ha,← Matrix.map_mul]
  rfl

theorem coordinate_eq_normalize (j : Fin 8) :
    coordinate ℂ j = normalize (quotientMatrix genericFrame) pivotEmbedding
      (coordinatePair j).2 (Fin.natAdd 2 (coordinatePair j).1) := by
  rw [genericNormalization_formula]
  change algebraMap P L (numerator ℂ j) / algebraMap P L (denominator ℂ) =
    (algebraMap P L (denominator ℂ))⁻¹ * algebraMap P L (numerator ℂ j)
  exact div_eq_inv_mul _ _

theorem normalize_map (g : Gamma) :
    (normalize (quotientMatrix genericFrame) pivotEmbedding).map
        (rationalRepresentation g).toRingHom =
      normalize (quotientMatrix (genericFrame.map (rationalRepresentation g).toRingHom))
        pivotEmbedding := by
  rw [QuotientMatrixKernels.normalize,Matrix.map_mul,matrixInverse_map _ _ genericPivot_unit,
    ← Matrix.submatrix_map,quotientMatrix_map]
  rfl

theorem coordinate_fixed (g : Gamma) (j : Fin 8) :
    rationalRepresentation g (coordinate ℂ j) = coordinate ℂ j := by
  rw [coordinate_eq_normalize]
  exact congrFun (congrFun ((normalize_map g).trans (normalize_generic_image g))
    (coordinatePair j).2) (Fin.natAdd 2 (coordinatePair j).1)

theorem targetFieldEmbedding_fixed (g : Gamma) (z : ConicFrameExtension.targetField ℂ) :
    rationalRepresentation g (ConicFrameExtension.targetFieldEmbedding ℂ z) =
      ConicFrameExtension.targetFieldEmbedding ℂ z := by
  have hp : (rationalRepresentation g).toAlgHom.comp
      ((toRationalAlgHom ℂ).comp (coordinateMap ℂ)) =
      (toRationalAlgHom ℂ).comp (coordinateMap ℂ) := by
    rw [toRational_coordinateMap]
    apply MvPolynomial.algHom_ext
    intro a
    simpa only [AlgHom.comp_apply,MvPolynomial.aeval_X,AlgEquiv.coe_toAlgHom] using
      coordinate_fixed g (coordinateEquiv a)
  have hh : (rationalRepresentation g).toRingHom.comp
      (ConicFrameExtension.targetFieldEmbedding ℂ).toRingHom =
      (ConicFrameExtension.targetFieldEmbedding ℂ).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := targetRing ℂ)
    intro p
    change rationalRepresentation g
      (ConicFrameExtension.targetFieldEmbedding ℂ
        (algebraMap (targetRing ℂ) (ConicFrameExtension.targetField ℂ) p)) =
      ConicFrameExtension.targetFieldEmbedding ℂ
        (algebraMap (targetRing ℂ) (ConicFrameExtension.targetField ℂ) p)
    rw [ConicFrameExtension.targetFieldEmbedding_algebraMap]
    exact DFunLike.congr_fun hp p
  exact DFunLike.congr_fun hh z

end M9Native.ConicFrameGammaInvariant
