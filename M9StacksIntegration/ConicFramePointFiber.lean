module

public import M9StacksIntegration.ConicFrameSourceMatrix
public import M9StacksIntegration.QuotientMatrixKernels
public import M9StacksIntegration.ConicFrameClosedFiber
public import M9StacksIntegration.ConicFrameExtension

/-!
# Actual algebraic point lifts and actual normalized conic-frame fibers

All points are actual complex algebra homomorphisms from the specified
localization. Matrix evaluation and reconstruction use the literal frame
entries, quotient matrix, and native Grassmannian chart coordinate map.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

namespace M9Native.ConicFramePointFiber

open ConicFrameProjective ConicFrameCoordinates ConicFrameCoordinateIndex
open ConicFrameSourceAlgebra ConicFrameSourceMatrix ConicFrameClosedFiber
open M9.ConicPencilFrames M9.ConicFourPlaneFrames

abbrev A := targetRing ℂ
abbrev B := sourceRing ℂ
abbrev P := polynomial ℂ
abbrev SourcePoint := B →ₐ[ℂ] ℂ

/-- Restriction of an actual localization point to its polynomial chart. -/
def polynomialPoint (y : SourcePoint) : P →ₐ[ℂ] ℂ :=
  y.comp (IsScalarTower.toAlgHom ℂ P B)

/-- The literal matrix of an actual point of the source localization. -/
def evaluatedFrame (y : SourcePoint) : Matrix3 := (sourceFrame ℂ).map y.toRingHom

theorem evaluatedFrame_eq (y : SourcePoint) :
    evaluatedFrame y = (normalizedFrame ℂ).map (polynomialPoint y).toRingHom := by
  rw [evaluatedFrame, sourceFrame, Matrix.map_map]
  rfl

theorem evaluatedFrame_det_unit (y : SourcePoint) : IsUnit (evaluatedFrame y).det := by
  rw [evaluatedFrame, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (sourceFrame_det_unit ℂ).map y.toRingHom

/-- The evaluated source frame is an actual invertible complex matrix. -/
def pointFrame (y : SourcePoint) : GL3 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (evaluatedFrame y) (evaluatedFrame_det_unit y).ne_zero

@[simp] theorem pointFrame_val (y : SourcePoint) : (pointFrame y : Matrix3) = evaluatedFrame y := rfl

theorem pointFrame_zero_zero (y : SourcePoint) : (pointFrame y : Matrix3) 0 0 = 1 := by
  simp [pointFrame_val, evaluatedFrame_eq, normalizedFrame]

theorem point_localizer_ne_zero (y : SourcePoint) : polynomialPoint y (localizer ℂ) ≠ 0 :=
  ((IsLocalization.Away.algebraMap_isUnit (S := B) (localizer ℂ)).map y.toRingHom).ne_zero

theorem pointFrame_firstRowNonzero (y : SourcePoint) : FirstRowNonzero (pointFrame y) := by
  have h := point_localizer_ne_zero y
  rw [localizer, map_mul, map_mul, map_mul] at h
  have h0 : polynomialPoint y (MvPolynomial.X 0) ≠ 0 :=
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h).1).2
  have h1 : polynomialPoint y (MvPolynomial.X 1) ≠ 0 := (mul_ne_zero_iff.mp h).2
  apply firstRowNonzero_of_normalized (pointFrame y) (pointFrame_zero_zero y)
  · change polynomialPoint y (MvPolynomial.X 0) ≠ 0
    exact h0
  · change polynomialPoint y (MvPolynomial.X 1) ≠ 0
    exact h1

theorem evaluatedQuotient (y : SourcePoint) :
    ConicFrame.quotientMatrix (evaluatedFrame y) =
      (ConicFrame.quotientMatrix (sourceFrame ℂ)).map y.toRingHom :=
  (ConicFrame.quotientMatrix_map y.toRingHom (sourceFrame ℂ)).symm

theorem evaluatedPivot (y : SourcePoint) :
    (ConicFrame.quotientMatrix (evaluatedFrame y)).submatrix id pivotEmbedding =
      ((ConicFrame.quotientMatrix (sourceFrame ℂ)).submatrix id pivotEmbedding).map y.toRingHom := by
  rw [evaluatedQuotient, Matrix.submatrix_map]

theorem pointFrame_pivot_unit (y : SourcePoint) :
    IsUnit ((ConicFrame.quotientMatrix (pointFrame y : Matrix3)).submatrix id pivotEmbedding).det := by
  rw [pointFrame_val, evaluatedPivot, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (sourcePivot_det_unit ℂ).map y.toRingHom

theorem evaluatedPivot_det (y : SourcePoint) :
    ((ConicFrame.quotientMatrix (evaluatedFrame y)).submatrix id pivotEmbedding).det =
      polynomialPoint y (denominator ℂ) := by
  rw [evaluatedPivot, ← RingHom.mapMatrix_apply, ← RingHom.map_det, sourcePivot_det_eq]
  rfl

/-- The actual normalized quotient matrix at a complex frame. -/
abbrev normalizedQuotient (F : GL3) :=
  QuotientMatrixKernels.normalize (ConicFrame.quotientMatrix (F : Matrix3)) pivotEmbedding

theorem evaluatedNormalizedMatrix (y : SourcePoint) :
    ((((ConicFrame.quotientMatrix (sourceFrame ℂ)).submatrix id pivotEmbedding)⁻¹ *
      ConicFrame.quotientMatrix (sourceFrame ℂ)).map y.toRingHom) = normalizedQuotient (pointFrame y) := by
  rw [Matrix.map_mul, matrixInverse_map y.toRingHom _ (sourcePivot_det_unit ℂ)]
  rw [← evaluatedPivot, ← evaluatedQuotient]
  rfl

theorem pointCoordinate_eq_entry (y : SourcePoint)
    (a : AlgebraicGeometry.Grassmannian.ChartIndex.{0} (k := 4) (n := 6) pivotEmbedding) :
    y (sourceCoordinate ℂ (coordinateEquiv a)) =
      normalizedQuotient (pointFrame y) a.down.2 a.down.1.val := by
  exact (congrArg y (sourceCoordinate_eq_entry ℂ a)).trans
    (congrFun (congrFun (evaluatedNormalizedMatrix y) a.down.2) a.down.1.val)

theorem normalizedQuotient_pivots (F : GL3)
    (hp : IsUnit ((ConicFrame.quotientMatrix (F : Matrix3)).submatrix id pivotEmbedding).det) :
    (normalizedQuotient F).submatrix id pivotEmbedding = 1 := by
  rw [normalizedQuotient, QuotientMatrixKernels.normalize,
    Matrix.submatrix_mul _ _ id id pivotEmbedding Function.bijective_id,
    Matrix.submatrix_id_id, Matrix.nonsing_inv_mul _ hp]

theorem normalize_kernel (Q : QuotientMatrixKernels.QMat ℂ)
    (hp : IsUnit (Q.submatrix id pivotEmbedding).det) :
    LinearMap.ker (QuotientMatrixKernels.normalize Q pivotEmbedding).mulVecLin =
      LinearMap.ker Q.mulVecLin := by
  ext v
  change ((Q.submatrix id pivotEmbedding)⁻¹ * Q).mulVec v = 0 ↔ Q.mulVec v = 0
  rw [← Matrix.mulVec_mulVec]
  constructor
  · intro h
    have hh := congrArg (Q.submatrix id pivotEmbedding).mulVec h
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hp, Matrix.one_mulVec,
      Matrix.mulVec_zero] at hh
    exact hh
  · intro h
    rw [h, Matrix.mulVec_zero]

theorem coordinatePullback_eq_iff_normalizedQuotient_eq (y z : SourcePoint) :
    y.comp (coordinateMap ℂ) = z.comp (coordinateMap ℂ) ↔
      normalizedQuotient (pointFrame y) = normalizedQuotient (pointFrame z) := by
  constructor
  · intro h
    ext i j
    by_cases hj : j ∈ Set.range pivotEmbedding
    · obtain ⟨j', rfl⟩ := hj
      exact (congrFun (congrFun (normalizedQuotient_pivots (pointFrame y) (pointFrame_pivot_unit y)) i) j').trans
        (congrFun (congrFun (normalizedQuotient_pivots (pointFrame z) (pointFrame_pivot_unit z)) i) j').symm
    · let a : AlgebraicGeometry.Grassmannian.ChartIndex.{0} (k := 4) (n := 6) pivotEmbedding :=
        ULift.up (⟨j, hj⟩, i)
      have hh := congrArg (fun f : A →ₐ[ℂ] ℂ => f (MvPolynomial.X a)) h
      simp only [AlgHom.comp_apply, coordinateMap, MvPolynomial.aeval_X] at hh
      simpa only [pointCoordinate_eq_entry] using hh
  · intro h
    apply MvPolynomial.algHom_ext
    intro a
    simp only [AlgHom.comp_apply, coordinateMap, MvPolynomial.aeval_X,
      pointCoordinate_eq_entry, h]

/-- Actual coordinate-map point fibers are exactly actual quotient-kernel
fibers, with no cardinality premise. -/
theorem coordinatePullback_eq_iff_kernel_eq (y z : SourcePoint) :
    y.comp (coordinateMap ℂ) = z.comp (coordinateMap ℂ) ↔
      quotientKernel (pointFrame y) = quotientKernel (pointFrame z) := by
  rw [coordinatePullback_eq_iff_normalizedQuotient_eq]
  constructor
  · intro h
    change LinearMap.ker (ConicFrame.quotientMatrix (pointFrame y : Matrix3)).mulVecLin =
      LinearMap.ker (ConicFrame.quotientMatrix (pointFrame z : Matrix3)).mulVecLin
    exact (normalize_kernel _ (pointFrame_pivot_unit y)).symm.trans
      ((congrArg (fun Q : QuotientMatrixKernels.QMat ℂ => LinearMap.ker Q.mulVecLin) h).trans
        (normalize_kernel _ (pointFrame_pivot_unit z)))
  · intro h
    exact QuotientMatrixKernels.normalize_eq_of_kernel_eq _ _ pivotEmbedding
      (ConicFrame.quotientMatrix_surjective _ (evaluatedFrame_det_unit y))
      (ConicFrame.quotientMatrix_surjective _ (evaluatedFrame_det_unit z)) h
      (pointFrame_pivot_unit y)

/-- The eight literal affine-frame entry positions. -/
def frameEntry : Fin 8 → Fin 3 × Fin 3 :=
  ![(0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)]

def matrixCoefficients (F : Matrix3) (i : Fin 8) : ℂ := F (frameEntry i).1 (frameEntry i).2

theorem polynomialPoint_X (y : SourcePoint) (i : Fin 8) :
    polynomialPoint y (MvPolynomial.X i) = matrixCoefficients (evaluatedFrame y) i := by
  fin_cases i <;> rfl

/-- Actual localization points are determined by their actual frame
matrices, using localization and polynomial extensionality. -/
theorem pointFrame_injective : Function.Injective pointFrame := by
  intro y z h
  apply IsLocalization.algHom_ext (Submonoid.powers (localizer ℂ))
  apply MvPolynomial.algHom_ext
  intro i
  change polynomialPoint y (MvPolynomial.X i) = polynomialPoint z (MvPolynomial.X i)
  rw [polynomialPoint_X, polynomialPoint_X]
  exact congrArg (fun F : GL3 => matrixCoefficients (F : Matrix3) i) h

/-- Polynomial evaluation at the eight literal entries of a frame. -/
def matrixPolynomialPoint (F : GL3) : P →ₐ[ℂ] ℂ :=
  MvPolynomial.aeval (matrixCoefficients (F : Matrix3))

theorem matrixPolynomialPoint_frame (F : GL3) (h00 : (F : Matrix3) 0 0 = 1) :
    (normalizedFrame ℂ).map (matrixPolynomialPoint F).toRingHom = (F : Matrix3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normalizedFrame, matrixPolynomialPoint, matrixCoefficients, frameEntry, h00]

theorem matrixPolynomialPoint_det (F : GL3) (h00 : (F : Matrix3) 0 0 = 1) :
    matrixPolynomialPoint F (normalizedFrame ℂ).det = (F : Matrix3).det := by
  change (matrixPolynomialPoint F).toRingHom (normalizedFrame ℂ).det = _
  rw [RingHom.map_det, RingHom.mapMatrix_apply, matrixPolynomialPoint_frame F h00]

theorem matrixPolynomialPoint_denominator (F : GL3) (h00 : (F : Matrix3) 0 0 = 1) :
    matrixPolynomialPoint F (denominator ℂ) =
      ((ConicFrame.quotientMatrix (F : Matrix3)).submatrix id pivotEmbedding).det := by
  have hp : (pivot ℂ).map (matrixPolynomialPoint F).toRingHom =
      (ConicFrame.quotientMatrix (F : Matrix3)).submatrix id pivotEmbedding := by
    rw [pivot, ← Matrix.submatrix_map, ConicFrame.quotientMatrix_map,
      matrixPolynomialPoint_frame F h00]
    rfl
  change (matrixPolynomialPoint F).toRingHom (pivot ℂ).det = _
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hp]

theorem matrixPolynomialPoint_localizer (F : GL3) (h00 : (F : Matrix3) 0 0 = 1) :
    matrixPolynomialPoint F (localizer ℂ) =
      (F : Matrix3).det * ((ConicFrame.quotientMatrix (F : Matrix3)).submatrix id pivotEmbedding).det *
        (F : Matrix3) 0 1 * (F : Matrix3) 0 2 := by
  rw [localizer, map_mul, map_mul, map_mul, matrixPolynomialPoint_det F h00,
    matrixPolynomialPoint_denominator F h00]
  simp [matrixPolynomialPoint, matrixCoefficients, frameEntry]

theorem matrixPolynomialPoint_localizer_ne_zero (F : GL3) (h00 : (F : Matrix3) 0 0 = 1)
    (hF : FirstRowNonzero F)
    (hp : IsUnit ((ConicFrame.quotientMatrix (F : Matrix3)).submatrix id pivotEmbedding).det) :
    matrixPolynomialPoint F (localizer ℂ) ≠ 0 := by
  rw [matrixPolynomialPoint_localizer F h00]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero
    (Matrix.GeneralLinearGroup.det_ne_zero F) hp.ne_zero) (hF 1)) (hF 2)

/-- Reconstruction as an actual algebra homomorphism from the actual
source localization, with its denominator condition proved. -/
def matrixPoint (F : GL3) (h00 : (F : Matrix3) 0 0 = 1) (hF : FirstRowNonzero F)
    (hp : IsUnit ((ConicFrame.quotientMatrix (F : Matrix3)).submatrix id pivotEmbedding).det) :
    SourcePoint :=
  IsLocalization.Away.liftAlgHom (localizer ℂ)
    (f := matrixPolynomialPoint F)
    (isUnit_iff_ne_zero.mpr (matrixPolynomialPoint_localizer_ne_zero F h00 hF hp))

@[simp] theorem matrixPoint_algebraMap (F : GL3) (h00 : (F : Matrix3) 0 0 = 1)
    (hF : FirstRowNonzero F)
    (hp : IsUnit ((ConicFrame.quotientMatrix (F : Matrix3)).submatrix id pivotEmbedding).det) (p : P) :
    matrixPoint F h00 hF hp (algebraMap P B p) = matrixPolynomialPoint F p :=
  IsLocalization.Away.lift_eq (localizer ℂ)
    (isUnit_iff_ne_zero.mpr (matrixPolynomialPoint_localizer_ne_zero F h00 hF hp)) p

theorem polynomialPoint_matrixPoint (F : GL3) (h00 : (F : Matrix3) 0 0 = 1)
    (hF : FirstRowNonzero F)
    (hp : IsUnit ((ConicFrame.quotientMatrix (F : Matrix3)).submatrix id pivotEmbedding).det) :
    polynomialPoint (matrixPoint F h00 hF hp) = matrixPolynomialPoint F := by
  apply AlgHom.ext
  intro p
  exact matrixPoint_algebraMap F h00 hF hp p

theorem pointFrame_matrixPoint (F : GL3) (h00 : (F : Matrix3) 0 0 = 1)
    (hF : FirstRowNonzero F)
    (hp : IsUnit ((ConicFrame.quotientMatrix (F : Matrix3)).submatrix id pivotEmbedding).det) :
    pointFrame (matrixPoint F h00 hF hp) = F := by
  apply Units.ext
  change evaluatedFrame (matrixPoint F h00 hF hp) = (F : Matrix3)
  rw [evaluatedFrame_eq, polynomialPoint_matrixPoint, matrixPolynomialPoint_frame F h00]

/-- Kernel equality transports the actual selected-minor condition, so
every matrix in the genuine normalized kernel fiber reconstructs a point
of this same localization. -/
theorem fiber_pivot_unit (y : SourcePoint) (N : NormalizedKernelFiber (pointFrame y)) :
    IsUnit ((ConicFrame.quotientMatrix (N.val : Matrix3)).submatrix id pivotEmbedding).det :=
  QuotientMatrixKernels.unit_minor_of_kernel_eq _ _ pivotEmbedding
    (ConicFrame.quotientMatrix_surjective _ (evaluatedFrame_det_unit y))
    (ConicFrame.quotientMatrix_surjective _
      (isUnit_iff_ne_zero.mpr (Matrix.GeneralLinearGroup.det_ne_zero N.val)))
    N.property.2.2 (pointFrame_pivot_unit y)

abbrev PointLifts (x : A →ₐ[ℂ] ℂ) := GenericEtaleFibreDegree.PointLifts ℂ A B x

/-- Evaluation gives an actual normalized matrix in the kernel fiber of
the chosen actual lift. -/
def liftToKernelFiber (x : A →ₐ[ℂ] ℂ) (y : PointLifts x) (z : PointLifts x) :
    NormalizedKernelFiber (pointFrame y.val) :=
  ⟨pointFrame z.val, pointFrame_zero_zero z.val, pointFrame_firstRowNonzero z.val,
    (coordinatePullback_eq_iff_kernel_eq y.val z.val).mp
      (y.property.trans z.property.symm)⟩

/-- Reconstruction produces an actual algebraic point lift, because
coordinate equality has been proved equivalent to literal kernel equality. -/
def kernelFiberToLift (x : A →ₐ[ℂ] ℂ) (y : PointLifts x)
    (N : NormalizedKernelFiber (pointFrame y.val)) : PointLifts x := by
  let z := matrixPoint N.val N.property.1 N.property.2.1 (fiber_pivot_unit y.val N)
  refine ⟨z, ?_⟩
  change z.comp (coordinateMap ℂ) = x
  calc
    z.comp (coordinateMap ℂ) = y.val.comp (coordinateMap ℂ) := by
      apply (coordinatePullback_eq_iff_kernel_eq z y.val).mpr
      rw [pointFrame_matrixPoint]
      exact N.property.2.2.symm
    _ = x := y.property

theorem kernelFiberToLift_frame (x : A →ₐ[ℂ] ℂ) (y : PointLifts x)
    (N : NormalizedKernelFiber (pointFrame y.val)) :
    pointFrame (kernelFiberToLift x y N).val = N.val := by
  change pointFrame (matrixPoint N.val N.property.1 N.property.2.1
    (fiber_pivot_unit y.val N)) = N.val
  exact pointFrame_matrixPoint N.val N.property.1 N.property.2.1 (fiber_pivot_unit y.val N)

/-- The actual point-lift fiber is equivalent to the actual normalized
matrix-kernel fiber of any chosen lift. No fiber count is assumed. -/
def pointLiftsEquivNormalizedKernelFiber (x : A →ₐ[ℂ] ℂ) (y : PointLifts x) :
    PointLifts x ≃ NormalizedKernelFiber (pointFrame y.val) where
  toFun := liftToKernelFiber x y
  invFun := kernelFiberToLift x y
  left_inv z := by
    apply Subtype.ext
    apply pointFrame_injective
    exact kernelFiberToLift_frame x y (liftToKernelFiber x y z)
  right_inv N := by
    apply Subtype.ext
    exact kernelFiberToLift_frame x y N

/-- Every nonempty actual complex algebraic fiber has exactly the
twenty-four points constructed by the genuine normalized tetrahedral action. -/
theorem card_pointLifts (x : A →ₐ[ℂ] ℂ) (hx : Nonempty (PointLifts x)) :
    Nat.card (PointLifts x) = 24 := by
  obtain ⟨y⟩ := hx
  exact (Nat.card_congr (pointLiftsEquivNormalizedKernelFiber x y)).trans
    (nat_card_normalizedKernelFiber (pointFrame y.val) (pointFrame_firstRowNonzero y.val))

end M9Native.ConicFramePointFiber
