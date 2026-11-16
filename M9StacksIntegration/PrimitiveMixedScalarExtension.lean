module

public import M9StacksIntegration.PrimitiveExtensionFieldBridge
public import M9StacksIntegration.ReducedGraphAction

/-!
# Original mixed coordinates under actual scalar extension

The mixed coordinates keep the frozen symmetric-matrix splitting and the
actual trace-dual splitting.  Their coefficient comparison is made through
the actual exterior basis, so it retains the original retraction matrix.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Module Matrix
open scoped TensorProduct BigOperators

namespace M9Native.PrimitiveMixedScalarExtension

open M9 M9.ExteriorPrimitive M9.PrimitiveBlockCoordinates M9.PrimitiveTwistedReduced
open M9.GraphBundleDescent

variable (K : Type) [Field K] [Algebra ℂ K]

local instance : CharZero K := PrimitiveExtensionFieldBridge.charZero_extension K
local instance primitiveGroup : AddCommGroup (Primitive K) :=
  { (Primitive K).addCommGroup with toAddCommMonoid := (Primitive K).addCommMonoid }
local instance complexPrimitiveGroup : AddCommGroup (Primitive ℂ) :=
  { (Primitive ℂ).addCommGroup with toAddCommMonoid := (Primitive ℂ).addCommMonoid }

/-- The same original mixed coordinates over an actual complex extension field. -/
def mixedCoordinates : Mixed K ≃ₗ[K] (Fin 12 → K) :=
  ((mixedDualEquiv K).trans
    ((symmetricSplit K).prodCongr (dualSymmetricSplit K))).trans
      GraphGrassmannianChart.ambientCoordinates

theorem mixedCoordinates_eq_actualCoordinates (z : Mixed K) :
    mixedCoordinates K z = ReducedGraphAction.actualCoordinates K (mixedDualEquiv K z) := rfl

theorem mixedCoordinates_complex : mixedCoordinates ℂ = PrimitiveRhoFiberChart.mixedCoordinates := rfl

/-- Literal coefficient extension of actual symmetric matrices. -/
def symmetricMap (Q : Symmetric3 ℂ) : Symmetric3 K :=
  ⟨Q.val.map (algebraMap ℂ K), by
    change (Q.val.map (algebraMap ℂ K)).transpose = Q.val.map (algebraMap ℂ K)
    rw [← Matrix.transpose_map, Q.property]⟩

theorem symmetricMap_entry (Q : Symmetric3 ℂ) (i j : Fin 3) :
    (symmetricMap K Q).val i j = algebraMap ℂ K (Q.val i j) := rfl

/-- The original exterior-coordinate functionals have the same literal
values on the coefficient-extended standard wedge basis. -/
theorem coordinate_basis_map (i j k : Fin 6) (b : Fin 20) :
    coordinate K i j k (LagrangianRing.thirdBasis20 K b) =
      algebraMap ℂ K (coordinate ℂ i j k (LagrangianRing.thirdBasis20 ℂ b)) := by
  simp only [LagrangianRing.thirdBasis20_apply, coordinate,
    exteriorPower.pairingDual_ιMulti_ιMulti]
  rw [RingHom.map_det]
  congr 1
  ext a b
  fin_cases b <;>
    simp [Matrix.of_apply, RingHom.mapMatrix_apply, LagrangianRing.basisVector, Pi.single_apply]

/-- Any literal scalar extension of all twenty exterior coefficients
preserves each original ordered coordinate functional. -/
theorem coordinate_of_coefficients (a : K) (w : Third ℂ) (v : Third K)
    (hv : ∀ b : Fin 20, (LagrangianRing.thirdBasis20 K).equivFun v b =
      algebraMap ℂ K ((LagrangianRing.thirdBasis20 ℂ).equivFun w b) * a)
    (i j k : Fin 6) :
    coordinate K i j k v = algebraMap ℂ K (coordinate ℂ i j k w) * a := by
  have hK := congrArg (coordinate K i j k) ((LagrangianRing.thirdBasis20 K).sum_repr v)
  have hC := congrArg (coordinate ℂ i j k) ((LagrangianRing.thirdBasis20 ℂ).sum_repr w)
  simp only [map_sum, map_smul, smul_eq_mul] at hK hC
  change (∑ b : Fin 20, (LagrangianRing.thirdBasis20 K).equivFun v b *
    coordinate K i j k (LagrangianRing.thirdBasis20 K b)) = coordinate K i j k v at hK
  change (∑ b : Fin 20, (LagrangianRing.thirdBasis20 ℂ).equivFun w b *
    coordinate ℂ i j k (LagrangianRing.thirdBasis20 ℂ b)) = coordinate ℂ i j k w at hC
  rw [← hK, ← hC, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [hv, coordinate_basis_map, map_mul]
  ring

theorem symmetricSplit_map (Q : Symmetric3 ℂ) :
    symmetricSplit K (symmetricMap K Q) =
      ((fun i => algebraMap ℂ K ((symmetricSplit ℂ Q).1 i)),
        fun i => algebraMap ℂ K ((symmetricSplit ℂ Q).2 i)) := rfl

/-- The exact original dual-coordinate test vectors extend coefficientwise. -/
theorem symmetricSplit_symm_basis_map (i : Fin 4 ⊕ Fin 2) :
    (symmetricSplit K).symm (ambientBasis K i) =
      symmetricMap K ((symmetricSplit ℂ).symm (ambientBasis ℂ i)) := by
  apply (symmetricSplit K).injective
  rw [LinearEquiv.apply_symm_apply, symmetricSplit_map]
  simp only [LinearEquiv.apply_symm_apply]
  cases i <;> apply Prod.ext <;> funext j <;> simp [ambientBasis, Pi.single_apply]

theorem tracePair_map (X Y : Symmetric3 ℂ) :
    M9.PrimitiveRepresentation.tracePair K (symmetricMap K X) (symmetricMap K Y) =
      algebraMap ℂ K (M9.PrimitiveRepresentation.tracePair ℂ X Y) := by
  change ((X.val.map (algebraMap ℂ K)) * (Y.val.map (algebraMap ℂ K))).trace =
    algebraMap ℂ K ((X.val * Y.val).trace)
  rw [← Matrix.map_mul, AddMonoidHom.map_trace]

theorem dualSymmetricSplit_trace_value (Y : Symmetric3 K) (i : Fin 4 ⊕ Fin 2) :
    Sum.elim (dualSymmetricSplit K (symmetricDualEquiv K Y)).1
        (dualSymmetricSplit K (symmetricDualEquiv K Y)).2 i =
      M9.PrimitiveRepresentation.tracePair K ((symmetricSplit K).symm (ambientBasis K i)) Y := by
  cases i with
  | inl j =>
      exact (ambientBasis K).dualBasis_equivFun
        ((symmetricSplit K).dualMap.symm (symmetricDualEquiv K Y)) (.inl j)
  | inr j =>
      exact (ambientBasis K).dualBasis_equivFun
        ((symmetricSplit K).dualMap.symm (symmetricDualEquiv K Y)) (.inr j)

/-- Coefficient extension preserves the actual trace-dual coordinates,
including their original off-diagonal normalization. -/
theorem dualSymmetricSplit_trace_map (Y : Symmetric3 ℂ) :
    dualSymmetricSplit K (symmetricDualEquiv K (symmetricMap K Y)) =
      ((fun i => algebraMap ℂ K ((dualSymmetricSplit ℂ (symmetricDualEquiv ℂ Y)).1 i)),
        fun i => algebraMap ℂ K ((dualSymmetricSplit ℂ (symmetricDualEquiv ℂ Y)).2 i)) := by
  apply Prod.ext
  · funext i
    change (dualSymmetricSplit K (symmetricDualEquiv K (symmetricMap K Y))).1 i =
      algebraMap ℂ K ((dualSymmetricSplit ℂ (symmetricDualEquiv ℂ Y)).1 i)
    have hK := dualSymmetricSplit_trace_value K (symmetricMap K Y) (.inl i)
    have hC := dualSymmetricSplit_trace_value ℂ Y (.inl i)
    change (dualSymmetricSplit K (symmetricDualEquiv K (symmetricMap K Y))).1 i = _ at hK
    change (dualSymmetricSplit ℂ (symmetricDualEquiv ℂ Y)).1 i = _ at hC
    rw [hK, hC, symmetricSplit_symm_basis_map, tracePair_map]
  · funext i
    change (dualSymmetricSplit K (symmetricDualEquiv K (symmetricMap K Y))).2 i =
      algebraMap ℂ K ((dualSymmetricSplit ℂ (symmetricDualEquiv ℂ Y)).2 i)
    have hK := dualSymmetricSplit_trace_value K (symmetricMap K Y) (.inr i)
    have hC := dualSymmetricSplit_trace_value ℂ Y (.inr i)
    change (dualSymmetricSplit K (symmetricDualEquiv K (symmetricMap K Y))).2 i = _ at hK
    change (dualSymmetricSplit ℂ (symmetricDualEquiv ℂ Y)).2 i = _ at hC
    rw [hK, hC, symmetricSplit_symm_basis_map, tracePair_map]

theorem mixedCoordinates_map (X Y : Symmetric3 ℂ) :
    mixedCoordinates K (symmetricMap K X, symmetricMap K Y) =
      (fun i => algebraMap ℂ K (mixedCoordinates ℂ (X,Y) i)) := by
  change GraphGrassmannianChart.ambientCoordinates
    (symmetricSplit K (symmetricMap K X),
      dualSymmetricSplit K (symmetricDualEquiv K (symmetricMap K Y))) = _
  rw [symmetricSplit_map, dualSymmetricSplit_trace_map]
  funext i
  change GraphGrassmannianChart.ambientCoordinates
    (((fun j => algebraMap ℂ K ((symmetricSplit ℂ X).1 j)),
      fun j => algebraMap ℂ K ((symmetricSplit ℂ X).2 j)),
      ((fun j => algebraMap ℂ K ((dualSymmetricSplit ℂ (symmetricDualEquiv ℂ Y)).1 j)),
        fun j => algebraMap ℂ K ((dualSymmetricSplit ℂ (symmetricDualEquiv ℂ Y)).2 j))) i =
    algebraMap ℂ K (GraphGrassmannianChart.ambientCoordinates
      (symmetricSplit ℂ X, dualSymmetricSplit ℂ (symmetricDualEquiv ℂ Y)) i)
  rw [GraphGrassmannianChart.ambientCoordinates_apply, GraphGrassmannianChart.ambientCoordinates_apply]
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin 4 ⊕ Fin 8 ≃ Fin 12).surjective i
  simp only [Equiv.symm_apply_apply]
  rcases i with i | i
  · rfl
  · obtain ⟨i, rfl⟩ := GraphGrassmannianChart.rowEquiv.surjective i
    simp only [Sum.elim_inr, Equiv.symm_apply_apply]
    rcases i with i | (i | i) <;> rfl

omit [Algebra ℂ K] in
theorem qExtraction_upper (w : Third K) (ij : Upper3) :
    symmetric3Coordinates K (qExtraction K w) ij = qCoordinate K ij.val.1 ij.val.2 w := by
  change (symmetric3Coordinates K) ((symmetric3Coordinates K).symm
    (fun ij : Upper3 => qCoordinate K ij.val.1 ij.val.2 w)) ij = _
  rw [LinearEquiv.apply_symm_apply]

omit [Algebra ℂ K] in
theorem pExtraction_upper (w : Third K) (ij : Upper3) :
    symmetric3Coordinates K (pExtraction K w) ij = pCoordinate K ij.val.1 ij.val.2 w := by
  change (symmetric3Coordinates K) ((symmetric3Coordinates K).symm
    (fun ij : Upper3 => pCoordinate K ij.val.1 ij.val.2 w)) ij = _
  rw [LinearEquiv.apply_symm_apply]

theorem qExtraction_scalarPrimitive (a : K) (w : Primitive ℂ) :
    qExtraction K (PrimitiveExtensionFieldBridge.scalarPrimitiveEquiv K (a ⊗ₜ[ℂ] w)).val =
      a • symmetricMap K (qExtraction ℂ w.val) := by
  apply (symmetric3Coordinates K).injective
  funext ij
  rw [qExtraction_upper, map_smul, Pi.smul_apply]
  change qCoordinate K ij.val.1 ij.val.2
    (PrimitiveExtensionFieldBridge.scalarPrimitiveEquiv K (a ⊗ₜ[ℂ] w)).val =
      a * algebraMap ℂ K (symmetric3Coordinates ℂ (qExtraction ℂ w.val) ij)
  rw [qExtraction_upper]
  have h := coordinate_of_coefficients K a w.val
    (PrimitiveExtensionFieldBridge.scalarPrimitiveEquiv K (a ⊗ₜ[ℂ] w)).val
    (fun b => congrFun (PrimitiveExtensionFieldBridge.scalarPrimitiveEquiv_tmul_coefficients K a w) b)
    (eIndex ij.val.1) (fIndex (nextOne ij.val.2)) (fIndex (nextTwo ij.val.2))
  exact h.trans (mul_comm _ _)

theorem pExtraction_scalarPrimitive (a : K) (w : Primitive ℂ) :
    pExtraction K (PrimitiveExtensionFieldBridge.scalarPrimitiveEquiv K (a ⊗ₜ[ℂ] w)).val =
      a • symmetricMap K (pExtraction ℂ w.val) := by
  apply (symmetric3Coordinates K).injective
  funext ij
  rw [pExtraction_upper, map_smul, Pi.smul_apply]
  change pCoordinate K ij.val.1 ij.val.2
    (PrimitiveExtensionFieldBridge.scalarPrimitiveEquiv K (a ⊗ₜ[ℂ] w)).val =
      a * algebraMap ℂ K (symmetric3Coordinates ℂ (pExtraction ℂ w.val) ij)
  rw [pExtraction_upper]
  have h := coordinate_of_coefficients K a w.val
    (PrimitiveExtensionFieldBridge.scalarPrimitiveEquiv K (a ⊗ₜ[ℂ] w)).val
    (fun b => congrFun (PrimitiveExtensionFieldBridge.scalarPrimitiveEquiv_tmul_coefficients K a w) b)
    (fIndex ij.val.1) (eIndex (nextOne ij.val.2)) (eIndex (nextTwo ij.val.2))
  exact h.trans (mul_comm _ _)

theorem mixedProjection_scalarPrimitive (a : K) (w : Primitive ℂ) :
    mixedProjection K (PrimitiveExtensionFieldBridge.scalarPrimitiveEquiv K (a ⊗ₜ[ℂ] w)) =
      (a • symmetricMap K ((mixedProjection ℂ w).1),
        a • symmetricMap K ((mixedProjection ℂ w).2)) :=
  Prod.ext (qExtraction_scalarPrimitive K a w) (pExtraction_scalarPrimitive K a w)

/-- The actual mixed projection of every pure scalar tensor keeps the frozen
complex coordinates and their original dual normalization. -/
theorem mixedCoordinates_scalarPrimitive_tmul (a : K) (w : Primitive ℂ) :
    mixedCoordinates K (mixedProjection K
      (PrimitiveExtensionFieldBridge.scalarPrimitiveEquiv K (a ⊗ₜ[ℂ] w))) =
      a • ((algebraMap ℂ K) ∘ PrimitiveRhoFiberChart.mixedCoordinateProjection w) := by
  rw [mixedProjection_scalarPrimitive]
  change mixedCoordinates K (a • (symmetricMap K ((mixedProjection ℂ w).1),
    symmetricMap K ((mixedProjection ℂ w).2))) = _
  rw [map_smul, mixedCoordinates_map]
  rfl

theorem retractionMatrix_coordinates (w : Primitive ℂ) :
    PrimitiveRhoFiberChart.retractionMatrix *ᵥ M9.PrimitiveRadicalScheme.primitiveCoordinates w =
      PrimitiveRhoFiberChart.mixedCoordinateProjection w := by
  rw [PrimitiveRhoFiberChart.retractionMatrix, LinearMap.toMatrix'_mulVec]
  change PrimitiveRhoFiberChart.mixedCoordinateProjection
    (M9.PrimitiveRadicalScheme.primitiveCoordinates.symm
      (M9.PrimitiveRadicalScheme.primitiveCoordinates w)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem fieldCoordinates_scalarPrimitive_tmul (a : K) (w : Primitive ℂ) :
    PrimitiveExtensionFieldBridge.fieldCoordinates K
      (PrimitiveExtensionFieldBridge.scalarPrimitiveEquiv K (a ⊗ₜ[ℂ] w)) =
      a • ((algebraMap ℂ K) ∘ M9.PrimitiveRadicalScheme.primitiveCoordinates w) := by
  rw [PrimitiveExtensionFieldBridge.scalarPrimitiveEquiv_coordinates]
  funext i
  rw [PrimitiveRadicalNativeScheme.scalarExtendedCoordinates_tmul]
  exact mul_comm _ _

/-- Actual scalar extension intertwines the frozen retraction matrix and
the original mixed projection on every tensor, not merely on dimensions. -/
theorem mixedCoordinates_retraction_scalar
    (w : K ⊗[ℂ] Primitive ℂ) :
    mixedCoordinates K (mixedProjection K (PrimitiveExtensionFieldBridge.scalarPrimitiveEquiv K w)) =
      PrimitiveRhoFiberChart.retractionMatrix.map (algebraMap ℂ K) *ᵥ
        PrimitiveExtensionFieldBridge.fieldCoordinates K
          (PrimitiveExtensionFieldBridge.scalarPrimitiveEquiv K w) := by
  let left : (K ⊗[ℂ] Primitive ℂ) →ₗ[K] (Fin 12 → K) :=
    (mixedCoordinates K).toLinearMap.comp
      ((mixedProjection K).comp (PrimitiveExtensionFieldBridge.scalarPrimitiveEquiv K).toLinearMap)
  let right : (K ⊗[ℂ] Primitive ℂ) →ₗ[K] (Fin 12 → K) :=
    (PrimitiveRhoFiberChart.retractionMatrix.map (algebraMap ℂ K)).mulVecLin.comp
      ((PrimitiveExtensionFieldBridge.fieldCoordinates K).toLinearMap.comp
        (PrimitiveExtensionFieldBridge.scalarPrimitiveEquiv K).toLinearMap)
  change left w = right w
  induction w using TensorProduct.inductionOn with
  | add x y hx hy => rw [left.map_add, right.map_add, hx, hy]
  | tmul a v =>
      change mixedCoordinates K (mixedProjection K
        (PrimitiveExtensionFieldBridge.scalarPrimitiveEquiv K (a ⊗ₜ[ℂ] v))) =
          PrimitiveRhoFiberChart.retractionMatrix.map (algebraMap ℂ K) *ᵥ
            PrimitiveExtensionFieldBridge.fieldCoordinates K
              (PrimitiveExtensionFieldBridge.scalarPrimitiveEquiv K (a ⊗ₜ[ℂ] v))
      rw [mixedCoordinates_scalarPrimitive_tmul, fieldCoordinates_scalarPrimitive_tmul,
        Matrix.mulVec_smul]
      congr 1
      funext i
      rw [← RingHom.map_mulVec, retractionMatrix_coordinates]
      rfl

/-- The exact original mixed-coordinate normalization over every complex
extension field, with the original frozen retraction matrix. -/
theorem mixedCoordinates_mixedProjection (v : Primitive K) :
    mixedCoordinates K (mixedProjection K v) =
      PrimitiveRhoFiberChart.retractionMatrix.map (algebraMap ℂ K) *ᵥ
        PrimitiveExtensionFieldBridge.fieldCoordinates K v := by
  obtain ⟨w, rfl⟩ := (PrimitiveExtensionFieldBridge.scalarPrimitiveEquiv K).surjective v
  exact mixedCoordinates_retraction_scalar K w

/-- The same literal identity in the actual symmetric-space plus dual-space
coordinates used by the native reduced Grassmannian action. -/
theorem actualCoordinates_mixedProjection (v : Primitive K) :
    ReducedGraphAction.actualCoordinates K (mixedDualEquiv K (mixedProjection K v)) =
      PrimitiveRhoFiberChart.retractionMatrix.map (algebraMap ℂ K) *ᵥ
        PrimitiveExtensionFieldBridge.fieldCoordinates K v :=
  mixedCoordinates_mixedProjection K v

end M9Native.PrimitiveMixedScalarExtension
