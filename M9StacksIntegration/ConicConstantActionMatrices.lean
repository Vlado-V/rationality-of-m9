module

public import M9StacksIntegration.ConicCompatibleGraphCoordinates

/-!
# Actual constant conic-coordinate action matrices under scalar extension

The canonical conic coordinates are retained, including the original
trace-dual equivalence. The original native representation is compared
through its proved actual-coordinate formula, never by identifying an
arbitrary old symmetric-space splitting across fields.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open Matrix

namespace M9Native.ConicConstantActionMatrices

open M9.PrimitiveBlockCoordinates M9.PrimitiveTwistedReduced
open ConicCompatibleGraphCoordinates

/-- The literal exchange of the first and second six-coordinate blocks. -/
def swapIndex : Equiv.Perm (Fin 12) :=
  (finSumFinEquiv : Fin 6 ⊕ Fin 6 ≃ Fin 12).symm.trans
    ((Equiv.sumComm (Fin 6) (Fin 6)).trans finSumFinEquiv)

/-- The actual zero-one block-swap matrix, in the original canonical order. -/
def swapMatrix (R : Type*) [CommRing R] : Matrix (Fin 12) (Fin 12) R :=
  fun i j => if swapIndex i = j then 1 else 0

theorem swapMatrix_mulVec {R : Type*} [CommRing R] (v : Fin 12 → R) :
    (swapMatrix R).mulVec v = v ∘ swapIndex := by
  classical
  funext i
  simp [swapMatrix, Matrix.mulVec, dotProduct, Function.comp_apply]

section Coordinates

variable (K : Type*) [Field K] [CharZero K]

/-- The actual native coordinates after the genuine trace-dual identification. -/
def pairCoordinates : Mixed K ≃ₗ[K] (Fin 12 → K) :=
  (mixedDualEquiv K).trans (actualCoordinates K)

/-- This is literally conic head (22,01,02,12), tail (00,11) on both factors. -/
theorem pairCoordinates_apply (z : Mixed K) :
    pairCoordinates K z = GraphGrassmannianChart.ambientCoordinates
      (conicSplit K z.1, conicSplit K z.2) := by
  change GraphGrassmannianChart.ambientCoordinates
      (conicSplit K z.1, traceSplit K (M9.PrimitiveBlockCoordinates.symmetricDualEquiv K z.2)) = _
  rw [traceSplit, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

/-- The connected formula is the proved original action, including its true trace dual. -/
theorem matrixRepresentation_connected_pair (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (z : Mixed K) :
    (matrixRepresentation K (SemidirectProduct.inl g)).val.mulVec (pairCoordinates K z) =
      pairCoordinates K (mixedAction K g z) := by
  have h := matrixRepresentation_actual K (SemidirectProduct.inl g) (mixedDualEquiv K z)
  rw [dualSemidirectRepresentation_apply, LinearEquiv.symm_apply_apply,
    mixedSemidirectRepresentation_inl] at h
  exact h

/-- The odd formula is the proved native trace-dual swap, in the same actual coordinates. -/
theorem matrixRepresentation_odd_pair (z : Mixed K) :
    (matrixRepresentation K (SemidirectProduct.inr M9.CentralSignQuotient.epsilon)).val.mulVec
        (pairCoordinates K z) = pairCoordinates K (z.2, z.1) := by
  have h := matrixRepresentation_actual K (SemidirectProduct.inr M9.CentralSignQuotient.epsilon)
    (mixedDualEquiv K z)
  rw [dualSemidirectRepresentation_apply, LinearEquiv.symm_apply_apply,
    mixedSemidirectRepresentation_inr_epsilon] at h
  exact h

theorem swapMatrix_pairCoordinates (z : Mixed K) :
    (swapMatrix K).mulVec (pairCoordinates K z) = pairCoordinates K (z.2,z.1) := by
  rw [swapMatrix_mulVec, pairCoordinates_apply, pairCoordinates_apply]
  funext i
  fin_cases i <;> rfl

/-- The actual odd native GL12 generator is literally the zero-one block exchange. -/
theorem matrixRepresentation_odd_literal :
    (matrixRepresentation K (SemidirectProduct.inr
      (Multiplicative.ofAdd (1 : ZMod 2)))).val = swapMatrix K := by
  apply Matrix.ext_of_mulVec_single
  intro j
  let z := (pairCoordinates K).symm (Pi.single j 1)
  have hz : pairCoordinates K z = Pi.single j 1 := (pairCoordinates K).apply_symm_apply _
  exact (congrArg ((matrixRepresentation K (SemidirectProduct.inr
      M9.CentralSignQuotient.epsilon)).val.mulVec) hz).symm.trans
    ((matrixRepresentation_odd_pair K z).trans
      ((swapMatrix_pairCoordinates K z).symm.trans (congrArg (swapMatrix K).mulVec hz)))

end Coordinates

section Maps

variable {R S : Type*} [Field R] [Field S] [CharZero R] [CharZero S] (φ : R →+* S)

/-- Entrywise scalar extension of an actual symmetric matrix. -/
def symmetricMap (Q : M9.Symmetric3 R) : M9.Symmetric3 S :=
  ⟨Q.val.map φ, by
    funext i j
    exact congrArg φ (congrFun (congrFun Q.property i) j)⟩

def mixedMap (z : Mixed R) : Mixed S :=
  (symmetricMap φ z.1, symmetricMap φ z.2)

theorem symmetricMap_congruence (F : Matrix (Fin 3) (Fin 3) R) (Q : M9.Symmetric3 R) :
    symmetricMap φ (M9.PrimitiveRepresentation.congruence R F Q) =
      M9.PrimitiveRepresentation.congruence S (F.map φ) (symmetricMap φ Q) := by
  apply Subtype.ext
  change (F * Q.val * F.transpose).map φ = F.map φ * Q.val.map φ * (F.map φ).transpose
  rw [Matrix.map_mul, Matrix.map_mul]
  rfl

/-- The fixed actual conic coordinates commute with the literal coefficient map. -/
theorem pairCoordinates_map (z : Mixed R) :
    pairCoordinates S (mixedMap φ z) = φ ∘ pairCoordinates R z := by
  rw [pairCoordinates_apply, pairCoordinates_apply]
  funext i
  fin_cases i <;> rfl

/-- Both actual connected matrix blocks commute with scalar extension;
the second retains its original inverse transpose. -/
theorem mixedMap_action (g : Matrix.SpecialLinearGroup (Fin 3) R) (z : Mixed R) :
    mixedMap φ (mixedAction R g z) =
      mixedAction S (Matrix.SpecialLinearGroup.map φ g) (mixedMap φ z) := by
  apply Prod.ext
  · exact symmetricMap_congruence φ g.val z.1
  · have hi : (g⁻¹).val.map φ = ((Matrix.SpecialLinearGroup.map φ g)⁻¹).val := by
      change (Matrix.SpecialLinearGroup.map φ (g⁻¹)).val = _
      exact congrArg Subtype.val (map_inv (Matrix.SpecialLinearGroup.map φ) g)
    have ht : ((g⁻¹).val.transpose).map φ = ((Matrix.SpecialLinearGroup.map φ g)⁻¹).val.transpose :=
      congrArg Matrix.transpose hi
    exact (symmetricMap_congruence φ (g⁻¹).val.transpose z.2).trans
      (congrArg (fun F => M9.PrimitiveRepresentation.congruence S F (symmetricMap φ z.2)) ht)

/-- Scalar extension of the original native connected GL12 generator, with no action premise. -/
theorem matrixRepresentation_connected_map_fieldHom (g : Matrix.SpecialLinearGroup (Fin 3) R) :
    Matrix.GeneralLinearGroup.map φ (matrixRepresentation R (SemidirectProduct.inl g)) =
      matrixRepresentation S (SemidirectProduct.inl (Matrix.SpecialLinearGroup.map φ g)) := by
  classical
  apply Units.ext
  let A := (matrixRepresentation R (SemidirectProduct.inl g)).val
  let B := (matrixRepresentation S
    (SemidirectProduct.inl (Matrix.SpecialLinearGroup.map φ g))).val
  change A.map φ = B
  apply Matrix.ext_of_mulVec_single
  intro j
  let z := (pairCoordinates R).symm (Pi.single j 1)
  have hz : pairCoordinates R z = Pi.single j 1 := (pairCoordinates R).apply_symm_apply _
  have hsingle : φ ∘ (Pi.single j (1 : R)) = (Pi.single j (1 : S)) := by
    funext i
    simp [Pi.single_apply]
  have hzmap : φ ∘ pairCoordinates R z = Pi.single j 1 :=
    (congrArg (fun v => φ ∘ v) hz).trans hsingle
  have hzS : pairCoordinates S (mixedMap φ z) = Pi.single j 1 :=
    (pairCoordinates_map φ z).trans hzmap
  calc
    _ = (A.map φ).mulVec (φ ∘ pairCoordinates R z) := congrArg (A.map φ).mulVec hzmap.symm
    _ = φ ∘ A.mulVec (pairCoordinates R z) :=
      funext (fun i => (RingHom.map_mulVec φ A (pairCoordinates R z) i).symm)
    _ = φ ∘ pairCoordinates R (mixedAction R g z) :=
      congrArg (fun v => φ ∘ v) (matrixRepresentation_connected_pair R g z)
    _ = pairCoordinates S (mixedMap φ (mixedAction R g z)) :=
      (pairCoordinates_map φ _).symm
    _ = pairCoordinates S
        (mixedAction S (Matrix.SpecialLinearGroup.map φ g) (mixedMap φ z)) :=
      congrArg (pairCoordinates S) (mixedMap_action φ g z)
    _ = B.mulVec (pairCoordinates S (mixedMap φ z)) :=
      (matrixRepresentation_connected_pair S (Matrix.SpecialLinearGroup.map φ g) (mixedMap φ z)).symm
    _ = _ := congrArg B.mulVec hzS

theorem swapMatrix_map : (swapMatrix R).map φ = swapMatrix S := by
  classical
  ext i j
  by_cases h : swapIndex i = j <;> simp [swapMatrix, h]

/-- The literal odd generator commutes with the actual coefficient-field map. -/
theorem matrixRepresentation_odd_map_fieldHom :
    Matrix.GeneralLinearGroup.map φ (matrixRepresentation R (SemidirectProduct.inr
      (Multiplicative.ofAdd (1 : ZMod 2)))) =
      matrixRepresentation S (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))) := by
  apply Units.ext
  change (matrixRepresentation R (SemidirectProduct.inr
      (Multiplicative.ofAdd (1 : ZMod 2)))).val.map φ = _
  rw [matrixRepresentation_odd_literal, matrixRepresentation_odd_literal]
  exact swapMatrix_map φ

end Maps

variable (K : Type*) [Field K] [CharZero K] [Algebra ℂ K]

/-- The actual constant complex SL3 generator in the extension field, in the fixed conic basis. -/
theorem matrixRepresentation_connected_map (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    Matrix.GeneralLinearGroup.map (algebraMap ℂ K)
        (matrixRepresentation ℂ (SemidirectProduct.inl g)) =
      matrixRepresentation K (SemidirectProduct.inl
        (Matrix.SpecialLinearGroup.map (algebraMap ℂ K) g)) :=
  matrixRepresentation_connected_map_fieldHom (algebraMap ℂ K) g

/-- The actual constant odd generator in the extension field is the same literal block swap. -/
theorem matrixRepresentation_odd_map :
    Matrix.GeneralLinearGroup.map (algebraMap ℂ K)
        (matrixRepresentation ℂ (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)))) =
      matrixRepresentation K (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))) :=
  matrixRepresentation_odd_map_fieldHom (algebraMap ℂ K)

end M9Native.ConicConstantActionMatrices
