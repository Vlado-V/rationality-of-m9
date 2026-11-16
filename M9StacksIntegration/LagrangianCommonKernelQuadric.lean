module

public import M9StacksIntegration.LagrangianCommonKernelSpan
public import M9StacksIntegration.LagrangianRingCoordinates

/-!
# The literal quadratic relation of the standard common-kernel coordinates

The five coordinates are the original q11,q12,q22,p00,b. Their quadratic
relation is proved over every commutative coefficient ring from actual
maximal minors and the actual row-isotropy equations. Thus nilpotents are
retained. This is the equation needed for the quadric in Mukai II4.4;
its converse scheme identification and finite intersection length bound
are separate geometric obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open Matrix Module

universe u

namespace M9Native.LagrangianCommonKernelQuadric

variable (R : Type u) [CommRing R]

/-- The actual ordered native maximal minor, preserving its column order. -/
def orderedMinor (M : Matrix (Fin 3) (Fin 6) R) (a b c : Fin 6) : R :=
  (M.submatrix id ![a,b,c]).det

/-- The literal surviving coordinates q11,q12,q22,p00,b. -/
def fiveCoordinates (M : Matrix (Fin 3) (Fin 6) R) : Fin 5 → R :=
  ![orderedMinor R M 1 5 3, orderedMinor R M 1 3 4,
    orderedMinor R M 2 3 4, orderedMinor R M 3 1 2, orderedMinor R M 3 4 5]

/-- The genuine maximal-minor Plucker relation, before imposing isotropy. -/
theorem orderedMinor_quadric_relation (M : Matrix (Fin 3) (Fin 6) R) :
    orderedMinor R M 1 5 3 * orderedMinor R M 2 3 4 -
      orderedMinor R M 1 3 4 * orderedMinor R M 2 5 3 =
      orderedMinor R M 3 1 2 * orderedMinor R M 3 4 5 := by
  norm_num [orderedMinor, Matrix.det_fin_three, Matrix.submatrix_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, id_eq]
  ring

/-- Row-isotropy is used through its literal original coefficients. -/
theorem mixed_minor_difference (M : Matrix (Fin 3) (Fin 6) R)
    (hM : ∀ i : Fin 3, M i 0 = 0) :
    orderedMinor R M 1 3 4 - orderedMinor R M 2 5 3 =
      -M 0 3 * LagrangianRing.omega R (M 1) (M 2) +
        M 1 3 * LagrangianRing.omega R (M 0) (M 2) -
        M 2 3 * LagrangianRing.omega R (M 0) (M 1) := by
  norm_num [orderedMinor, Matrix.det_fin_three, Matrix.submatrix_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, id_eq,
    LagrangianRing.omega_apply, LagrangianRing.omegaValue, Fin.sum_univ_succ,
    LagrangianRing.eIndex, LagrangianRing.fIndex, hM]
  ring

theorem mixed_minors_equal_of_isotropic (M : Matrix (Fin 3) (Fin 6) R)
    (hM : ∀ i : Fin 3, M i 0 = 0)
    (hiso : ∀ i j : Fin 3, LagrangianRing.omega R (M i) (M j) = 0) :
    orderedMinor R M 1 3 4 = orderedMinor R M 2 5 3 := by
  apply sub_eq_zero.mp
  rw [mixed_minor_difference R M hM]
  simp only [hiso, mul_zero, add_zero, sub_zero]

/-- The actual standard common-kernel quotient satisfies the literal
quadric equation over the original coefficient ring, including nilpotents. -/
theorem fiveCoordinates_quadric (M : Matrix (Fin 3) (Fin 6) R)
    (hM : ∀ i : Fin 3, M i 0 = 0)
    (hiso : ∀ i j : Fin 3, LagrangianRing.omega R (M i) (M j) = 0) :
    fiveCoordinates R M 0 * fiveCoordinates R M 2 -
      fiveCoordinates R M 1 * fiveCoordinates R M 1 =
      fiveCoordinates R M 3 * fiveCoordinates R M 4 := by
  have h := orderedMinor_quadric_relation R M
  rw [← mixed_minors_equal_of_isotropic R M hM hiso] at h
  exact h

section OriginalFieldCoordinates

open LagrangianField

variable (K : Type u) [Field K]

private theorem qExtraction_upper (w : Third K) (i j : Fin 3) (hij : i ≤ j) :
    (qExtraction K w).val i j = qCoordinate K i j w := by
  change upperMatrix (fun ij : Upper3 => qCoordinate K ij.val.1 ij.val.2 w) i j = _
  simp [upperMatrix, hij]

private theorem pExtraction_upper (w : Third K) (i j : Fin 3) (hij : i ≤ j) :
    (pExtraction K w).val i j = pCoordinate K i j w := by
  change upperMatrix (fun ij : Upper3 => pCoordinate K ij.val.1 ij.val.2 w) i j = _
  simp [upperMatrix, hij]

/-- The coordinates above are exactly the original five-coordinate
extraction already used for the actual primitive span, with no reindexing. -/
theorem fiveCoordinates_eq_original (M : Matrix (Fin 3) (Fin 6) K) :
    fiveCoordinates K M = LagrangianCommonKernelSpan.extraction K
      (coordinateProjection K (rowPlucker K M)) := by
  funext a
  fin_cases a
  · change orderedMinor K M 1 5 3 = (qExtraction K (rowPlucker K M)).val 1 1
    rw [qExtraction_upper K _ 1 1 (by decide)]
    simp [orderedMinor, qCoordinate, rowPlucker, coordinate_wedge3, nextOne, nextTwo,
      eIndex, fIndex, Matrix.det_fin_three]
    ring
  · change orderedMinor K M 1 3 4 = (qExtraction K (rowPlucker K M)).val 1 2
    rw [qExtraction_upper K _ 1 2 (by decide)]
    simp [orderedMinor, qCoordinate, rowPlucker, coordinate_wedge3, nextOne, nextTwo,
      eIndex, fIndex, Matrix.det_fin_three]
    ring
  · change orderedMinor K M 2 3 4 = (qExtraction K (rowPlucker K M)).val 2 2
    rw [qExtraction_upper K _ 2 2 (by decide)]
    simp [orderedMinor, qCoordinate, rowPlucker, coordinate_wedge3, nextOne, nextTwo,
      eIndex, fIndex, Matrix.det_fin_three]
    ring
  · change orderedMinor K M 3 1 2 = (pExtraction K (rowPlucker K M)).val 0 0
    rw [pExtraction_upper K _ 0 0 (by decide)]
    simp [orderedMinor, pCoordinate, rowPlucker, coordinate_wedge3, nextOne, nextTwo,
      eIndex, fIndex, Matrix.det_fin_three]
    ring
  · change orderedMinor K M 3 4 5 = bCoordinate K (rowPlucker K M)
    simp [orderedMinor, bCoordinate, rowPlucker, coordinate_wedge3, Matrix.det_fin_three]
    ring

end OriginalFieldCoordinates

end M9Native.LagrangianCommonKernelQuadric
