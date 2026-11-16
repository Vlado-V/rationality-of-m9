module

public import M9StacksIntegration.LagrangianRingCoordinates

/-! The fixed fourteen primitive coordinate rows commute with a genuine
field homomorphism. The proof uses their actual ordered exterior basis
and coefficient-extraction formulas, preserving the fixed ordering. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open Module Matrix exteriorPower
open M9Native.LagrangianField

universe u

namespace M9Native.LagrangianCoordinateFieldChange

variable {K L : Type u} [Field K] [Field L] (φ : K →+* L)

def coordinateIndexEquiv : CoordinateIndex ≃ Fin 14 :=
  Fintype.equivFinOfCardEq (by simp [CoordinateIndex])

theorem projectionMatrix_apply (K : Type u) [Field K] (j : Fin 14) (i : Fin 20) :
    projectionMatrix K j i =
      match coordinateIndexEquiv.symm j with
      | .inl _ => aCoordinate K (thirdBasis20 K i)
      | .inr (.inl ij) => qCoordinate K ij.val.1 ij.val.2 (thirdBasis20 K i)
      | .inr (.inr (.inl ij)) => pCoordinate K ij.val.1 ij.val.2 (thirdBasis20 K i)
      | .inr (.inr (.inr _)) => bCoordinate K (thirdBasis20 K i) := by
  rw [projectionMatrix, LinearMap.toMatrix_apply]
  change (coordinateBasis K).repr (coordinateProjection K (thirdBasis20 K i))
    (coordinateIndexEquiv.symm j) = _
  generalize coordinateIndexEquiv.symm j = x
  rcases x with x | x
  · simp [coordinateBasis, coordinateProjection]
  · rcases x with ij | x
    · simp [coordinateBasis, coordinateProjection, qExtraction]
    · rcases x with ij | x
      · simp [coordinateBasis, coordinateProjection, pExtraction]
      · simp [coordinateBasis, coordinateProjection]

theorem thirdBasis20_eq_wedge (K : Type u) [Field K] (i : Fin 20) :
    thirdBasis20 K i = wedge3 K
      (basisVector K (LagrangianRing.triple i 0))
      (basisVector K (LagrangianRing.triple i 1))
      (basisVector K (LagrangianRing.triple i 2)) := by
  rw [← LagrangianRing.thirdBasis20_eq_field, LagrangianRing.thirdBasis20_apply]
  unfold wedge3
  congr 1
  funext j
  fin_cases j <;> rfl

theorem coordinate_basis_map (a b c : Fin 6) (i : Fin 20) :
    φ (coordinate K a b c (thirdBasis20 K i)) =
      coordinate L a b c (thirdBasis20 L i) := by
  rw [thirdBasis20_eq_wedge, thirdBasis20_eq_wedge,
    coordinate_wedge3, coordinate_wedge3]
  simp only [basisVector, Pi.single_apply, map_add, map_sub, map_mul]
  split_ifs <;> simp

/-- The actual primitive-coordinate projection matrix is literally
natural under the supplied field homomorphism. -/
theorem projectionMatrix_map : (projectionMatrix K).map φ = projectionMatrix L := by
  ext j i
  simp only [Matrix.map_apply, projectionMatrix_apply]
  generalize coordinateIndexEquiv.symm j = x
  rcases x with x | x
  · exact coordinate_basis_map φ 0 1 2 i
  · rcases x with ij | x
    · exact coordinate_basis_map φ (eIndex ij.val.1)
        (fIndex (nextOne ij.val.2)) (fIndex (nextTwo ij.val.2)) i
    · rcases x with ij | x
      · exact coordinate_basis_map φ (fIndex ij.val.1)
          (eIndex (nextOne ij.val.2)) (eIndex (nextTwo ij.val.2)) i
      · exact coordinate_basis_map φ 3 4 5 i

end M9Native.LagrangianCoordinateFieldChange
