module

public import M9StacksIntegration.LagrangianPluckerFirstJet
public import M9StacksIntegration.LagrangianPluckerFactor

/-! The exact finite reindex of the original primitive coordinate basis.
No numerical `Fin 14` numbering is chosen or assumed. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open Module

universe u

namespace M9Native.LagrangianCoordinateBasisEntries

open LagrangianField

def indexEquiv : CoordinateIndex ≃ Fin 14 :=
  Fintype.equivFinOfCardEq (by simp [CoordinateIndex])

variable (K : Type u) [Field K]

def blockValue (r : Coordinates K) : CoordinateIndex → K :=
  Sum.elim (fun _ => r.1)
    (Sum.elim (fun ij => r.2.1.val ij.val.1 ij.val.2)
      (Sum.elim (fun ij => r.2.2.1.val ij.val.1 ij.val.2) (fun _ => r.2.2.2)))

theorem coordinateBasis_repr (r : Coordinates K) (i : CoordinateIndex) :
    (coordinateBasis K).repr r i = blockValue K r i := by
  cases i with
  | inl i => simp [coordinateBasis, blockValue]
  | inr i =>
    cases i with
    | inl ij =>
      simp [coordinateBasis, blockValue, Basis.map_repr, symmetric3Coordinates]
    | inr i =>
      cases i with
      | inl ij =>
        simp [coordinateBasis, blockValue, Basis.map_repr, symmetric3Coordinates]
      | inr i => simp [coordinateBasis, blockValue]

theorem coordinateBasis14_reindex :
    coordinateBasis14 K = (coordinateBasis K).reindex indexEquiv := rfl

theorem coordinateBasis14_repr (r : Coordinates K) (i : CoordinateIndex) :
    (coordinateBasis14 K).repr r (indexEquiv i) = blockValue K r i := by
  rw [coordinateBasis14_reindex, Basis.repr_reindex_apply, Equiv.symm_apply_apply]
  exact coordinateBasis_repr K r i

def extraction : CoordinateIndex → Third K →ₗ[K] K :=
  Sum.elim (fun _ => aCoordinate K)
    (Sum.elim (fun ij => qCoordinate K ij.val.1 ij.val.2)
      (Sum.elim (fun ij => pCoordinate K ij.val.1 ij.val.2) (fun _ => bCoordinate K)))

theorem coordinateProjection_blockValue (w : Third K) (i : CoordinateIndex) :
    blockValue K (coordinateProjection K w) i = extraction K i w := by
  cases i with
  | inl i => rfl
  | inr i =>
    cases i with
    | inl ij =>
      simp [blockValue, coordinateProjection, extraction, qExtraction,
        symmetric3Coordinates, upperMatrix, ij.property]
    | inr i =>
      cases i with
      | inl ij =>
        simp [blockValue, coordinateProjection, extraction, pExtraction,
          symmetric3Coordinates, upperMatrix, ij.property]
      | inr i => rfl

theorem coordinateBasis14_projection (w : Third K) (i : CoordinateIndex) :
    (coordinateBasis14 K).equivFun (coordinateProjection K w) (indexEquiv i) =
      extraction K i w := by
  rw [Basis.equivFun_apply, coordinateBasis14_repr, coordinateProjection_blockValue]

theorem projectionMatrix_entry (i : CoordinateIndex) (j : Fin 20) :
    projectionMatrix K (indexEquiv i) j = extraction K i (thirdBasis20 K j) := by
  rw [projectionMatrix, LinearMap.toMatrix_apply]
  change (coordinateBasis14 K).repr (coordinateProjection K (thirdBasis20 K j)) (indexEquiv i) = _
  exact (coordinateBasis14_repr K _ i).trans (coordinateProjection_blockValue K _ i)

end M9Native.LagrangianCoordinateBasisEntries
