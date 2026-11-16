module

public import M9StacksIntegration.ConicMovingBaseCoordinates
public import M9StacksIntegration.GenericConicTensorCoordinates
public import M9StacksIntegration.ConicGraphBaseCoordinates

/-! The original rational conic-cover coordinates are exactly the negative
entries of the actual generic moving-plane cell. All generic minors are
proved nonzero in the original polynomial fraction field. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

open Matrix
open scoped Classical

namespace M9Native.GenericConicBaseCoordinates

open GenericConicHead ConicFrameSourceMatrix ConicFrameSourceAlgebra
open ConicGraphBaseCoordinates ConicFrameCoordinateIndex
open ConicMovingBaseCoordinates

def sourceToField : ConicFrameProjective.polynomial ℂ →ₐ[ℂ] L :=
  IsScalarTower.toAlgHom ℂ (ConicFrameProjective.polynomial ℂ) L

theorem sourceFrame_toRational :
    (sourceFrame ℂ).map (toRationalAlgHom ℂ).toRingHom = genericFrameUnit.val := by
  apply Matrix.ext
  intro i j
  exact toRational_algebraMap ℂ (ConicFrameProjective.normalizedFrame ℂ i j)

theorem sourceQuotient_toRational :
    (ConicFrame.quotientMatrix (sourceFrame ℂ)).map (toRationalAlgHom ℂ).toRingHom =
      ConicFrame.quotientMatrix genericFrameUnit.val :=
  (ConicFrame.quotientMatrix_map _ _).trans
    (congrArg ConicFrame.quotientMatrix sourceFrame_toRational)

theorem genericPivotUnit :
    IsUnit ((ConicFrame.quotientMatrix genericFrameUnit.val).submatrix id (Fin.castAdd 4)).det := by
  have h := (sourcePivot_det_unit ℂ).map (toRationalAlgHom ℂ).toRingHom
  rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map,
    sourceQuotient_toRational] at h
  exact h

theorem sourceNormalized_toRational :
    ((((ConicFrame.quotientMatrix (sourceFrame ℂ)).submatrix id pivotEmbedding)⁻¹ *
      ConicFrame.quotientMatrix (sourceFrame ℂ)).map (toRationalAlgHom ℂ).toRingHom) =
      normalizedQuotient L genericFrameUnit := by
  rw [Matrix.map_mul, matrixInverse_map (toRationalAlgHom ℂ).toRingHom _
    (sourcePivot_det_unit ℂ), ← Matrix.submatrix_map, sourceQuotient_toRational]
  rfl

theorem genericCoordinate (a : NativeIndex) :
    ConicFrameCoordinates.coordinate ℂ (coordinateEquiv a) =
      normalizedQuotient L genericFrameUnit a.down.2 a.down.1.val := by
  calc
    ConicFrameCoordinates.coordinate ℂ (coordinateEquiv a) =
        toRationalAlgHom ℂ (sourceCoordinate ℂ (coordinateEquiv a)) :=
      (toRational_sourceCoordinate ℂ (coordinateEquiv a)).symm
    _ = toRationalAlgHom ℂ
        ((((ConicFrame.quotientMatrix (sourceFrame ℂ)).submatrix id pivotEmbedding)⁻¹ *
          ConicFrame.quotientMatrix (sourceFrame ℂ)) a.down.2 a.down.1.val) :=
      congrArg (toRationalAlgHom ℂ) (sourceCoordinate_eq_entry ℂ a)
    _ = _ := congrFun (congrFun sourceNormalized_toRational a.down.2) a.down.1.val

theorem oneIndex_coordinate (i : Fin 2) (j : Fin 4) :
    coordinateEquiv (oneIndexEquiv (i,j)) = finProdFinEquiv (j,i) := by
  simp [oneIndexEquiv]

theorem oneIndex_row (i : Fin 2) (j : Fin 4) : (oneIndexEquiv (i,j)).down.2 = i := by
  have h := coordinateEquiv_symm_row.{0} (finProdFinEquiv (j,i))
  change (oneIndexEquiv (i,j)).down.2 =
    ((finProdFinEquiv : Fin 4 × Fin 2 ≃ Fin 8).symm (finProdFinEquiv (j,i))).2 at h
  exact h.trans (congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (j,i)))

theorem oneIndex_column (i : Fin 2) (j : Fin 4) :
    (oneIndexEquiv (i,j)).down.1.val = Fin.natAdd 2 j := by
  have h := coordinateEquiv_symm_column.{0} (finProdFinEquiv (j,i))
  change (oneIndexEquiv (i,j)).down.1.val =
    Fin.natAdd 2 ((finProdFinEquiv : Fin 4 × Fin 2 ≃ Fin 8).symm (finProdFinEquiv (j,i))).1 at h
  exact h.trans (congrArg (fun x : Fin 4 × Fin 2 => Fin.natAdd 2 x.1)
    (finProdFinEquiv.symm_apply_apply (j,i)))

/-- Literal native quotient coordinates equal the negatives of the actual
moving cell matrix; no function-field identification premise is supplied. -/
theorem coordinate_eq_neg_genericPlane (i : Fin 2) (j : Fin 4) :
    ConicFrameCoordinates.coordinate ℂ (finProdFinEquiv (j,i)) = - genericPlaneMatrix i j := by
  have h := genericCoordinate (oneIndexEquiv (i,j))
  rw [oneIndex_coordinate, oneIndex_row, oneIndex_column] at h
  exact h.trans ((normalizedQuotient_nonpivot L genericFrameUnit
    GenericConicTensorCoordinates.headCondition genericPivotUnit i j).trans
      (congrArg (fun A : M9.GraphBundleDescent.BaseMatrix L => - A i j)
        GenericConicTensorCoordinates.cellMatrix_eq))

end M9Native.GenericConicBaseCoordinates
