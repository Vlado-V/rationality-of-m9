module

public import M9StacksIntegration.ReducedGraphTwistedAction
public import M9StacksIntegration.ConicFrameBaseChange
public import M9.MovingScalarExtendedGraphFrames

/-! A literal conic-compatible coordinate chart for the actual reduced space.
The original native action is retained through the proved constant GL12
scheme change of basis. No function-field identification is supplied. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix

namespace M9Native.ConicCompatibleGraphCoordinates

open M9.GraphBundleDescent M9.PrimitiveTwistedReduced

variable (K : Type*) [Field K] [CharZero K]

abbrev H := ReducedGraphAction.Stabilizer K
abbrev Coord := Fin 12 → K

/-- Actual symmetric matrices in the same six coordinates as the real conic map. -/
def conicCoordinates : M9.Symmetric3 K ≃ₗ[K] (Fin 6 → K) where
  toFun Q := ConicFrame.symCoordinates Q.val
  invFun v := ⟨ConicFrame.symMatrix v, ConicFrame.symMatrix_transpose v⟩
  left_inv Q := Subtype.ext (ConicFrame.symMatrix_symCoordinates Q.val Q.property)
  right_inv := ConicFrame.symCoordinates_symMatrix
  map_add' Q R := by ext i; fin_cases i <;> rfl
  map_smul' c Q := by ext i; fin_cases i <;> rfl

omit [CharZero K] in
theorem conicCoordinates_congruence (F : Matrix (Fin 3) (Fin 3) K) (Q : M9.Symmetric3 K) :
    conicCoordinates K (M9.PrimitiveRepresentation.congruence K F Q) =
      (ConicFrame.congruence F).mulVec (conicCoordinates K Q) := by
  change ConicFrame.symCoordinates (F * Q.val * F.transpose) =
    (ConicFrame.congruence F).mulVec (ConicFrame.symCoordinates Q.val)
  rw [ConicFrame.congruence_mulVec, ConicFrame.symMatrix_symCoordinates Q.val Q.property]

/-- Head is (22,01,02,12), tail is (00,11). -/
def splitSix : (Fin 6 → K) ≃ₗ[K] Ambient K :=
  (LinearEquiv.funCongrLeft K K (finSumFinEquiv : Fin 2 ⊕ Fin 4 ≃ Fin 6)).trans
    ((LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin 4) K K).trans
      (LinearEquiv.prodComm K (Fin 2 → K) (Fin 4 → K)))

omit [CharZero K] in
theorem splitSix_head (v : Fin 6 → K) (i : Fin 4) :
    (splitSix K v).1 i = v (Fin.natAdd 2 i) := rfl

omit [CharZero K] in
theorem splitSix_tail (v : Fin 6 → K) (i : Fin 2) :
    (splitSix K v).2 i = v (Fin.castAdd 4 i) := rfl

def conicSplit : M9.Symmetric3 K ≃ₗ[K] Ambient K :=
  (conicCoordinates K).trans (splitSix K)

/-- The second coordinates use the proved actual trace duality. -/
def traceSplit : Module.Dual K (M9.Symmetric3 K) ≃ₗ[K] Ambient K :=
  (M9.PrimitiveBlockCoordinates.symmetricDualEquiv K).symm.trans (conicSplit K)

def actualCoordinates : DualMixed K ≃ₗ[K] Coord K :=
  ((conicSplit K).prodCongr (traceSplit K)).trans GraphGrassmannianChart.ambientCoordinates

/-- Literal constant change from the frozen original reduced coordinates. -/
def basisChangeLinear : Coord K ≃ₗ[K] Coord K :=
  (ReducedGraphAction.actualCoordinates K).symm.trans (actualCoordinates K)

def basisChange : Matrix.GeneralLinearGroup (Fin 12) K :=
  ReducedGraphAction.coordinateGL K (basisChangeLinear K)

theorem basisChange_actual (z : DualMixed K) :
    (basisChange K).val.mulVec (ReducedGraphAction.actualCoordinates K z) = actualCoordinates K z := by
  rw [basisChange, ReducedGraphAction.coordinateGL_mulVec]
  change actualCoordinates K
    ((ReducedGraphAction.actualCoordinates K).symm (ReducedGraphAction.actualCoordinates K z)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem basisChange_inv_actual (z : DualMixed K) :
    (basisChange K)⁻¹.val.mulVec (actualCoordinates K z) = ReducedGraphAction.actualCoordinates K z := by
  have h := congrArg (fun v : Coord K => (basisChange K)⁻¹.val.mulVec v) (basisChange_actual K z)
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h
  exact h.symm

def matrixRepresentation : H K →* Matrix.GeneralLinearGroup (Fin 12) K :=
  (MulAut.conj (basisChange K)).toMonoidHom.comp (ReducedGraphAction.matrixRepresentation K)

/-- This remains the actual reduced primitive representation in the new coordinates. -/
theorem matrixRepresentation_actual (w : H K) (z : DualMixed K) :
    (matrixRepresentation K w).val.mulVec (actualCoordinates K z) =
      actualCoordinates K (dualSemidirectRepresentation K w z) := by
  change ((basisChange K).val * (ReducedGraphAction.matrixRepresentation K w).val *
    (basisChange K)⁻¹.val).mulVec (actualCoordinates K z) = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, basisChange_inv_actual,
    ReducedGraphAction.matrixRepresentation_actual, basisChange_actual]

def nativeAction (w : H K) : GrassmannianCharts.space K 4 12 ⟶ GrassmannianCharts.space K 4 12 :=
  GraphGrassmannianLinearAction.action K (matrixRepresentation K w)

instance nativeAction_isDominant (w : H K) : IsDominant (nativeAction K w) := by
  unfold nativeAction
  infer_instance

def nativeFieldRepresentation : H K →*
    ((GrassmannianCharts.space K 4 12).functionField ≃ₐ[K]
      (GrassmannianCharts.space K 4 12).functionField) :=
  (GraphGrassmannianLinearAction.fieldRepresentation K).comp (matrixRepresentation K)

def basisScheme : GrassmannianCharts.space K 4 12 ≅ GrassmannianCharts.space K 4 12 :=
  GraphGrassmannianLinearAction.rightAutomorphism K (basisChange K)⁻¹

def basisField : (GrassmannianCharts.space K 4 12).functionField ≃ₐ[K]
    (GrassmannianCharts.space K 4 12).functionField :=
  GraphGrassmannianLinearAction.fieldAutomorphism K (basisChange K)⁻¹

/-- Genuine native scheme equivariance of this actual ambient basis change. -/
theorem basisScheme_equivariance (w : H K) :
    ReducedGraphAction.nativeAction K w ≫ (basisScheme K).hom =
      (basisScheme K).hom ≫ nativeAction K w := by
  change GraphGrassmannianLinearAction.action K (ReducedGraphAction.matrixRepresentation K w) ≫
      GraphGrassmannianLinearAction.action K (basisChange K)⁻¹ =
    GraphGrassmannianLinearAction.action K (basisChange K)⁻¹ ≫
      GraphGrassmannianLinearAction.action K (matrixRepresentation K w)
  rw [GraphGrassmannianLinearAction.action_mul, GraphGrassmannianLinearAction.action_mul]
  congr 1
  change ReducedGraphAction.matrixRepresentation K w * (basisChange K)⁻¹ =
    (basisChange K)⁻¹ * (basisChange K * ReducedGraphAction.matrixRepresentation K w * (basisChange K)⁻¹)
  group

theorem basisField_equivariance (w : H K)
    (z : (GrassmannianCharts.space K 4 12).functionField) :
    basisField K (nativeFieldRepresentation K w z) =
      ReducedGraphAction.nativeFieldRepresentation K w (basisField K z) := by
  change GraphGrassmannianLinearAction.fieldRepresentation K (basisChange K)⁻¹
      (GraphGrassmannianLinearAction.fieldRepresentation K (matrixRepresentation K w) z) =
    GraphGrassmannianLinearAction.fieldRepresentation K (ReducedGraphAction.matrixRepresentation K w)
      (GraphGrassmannianLinearAction.fieldRepresentation K (basisChange K)⁻¹ z)
  rw [← AlgEquiv.mul_apply, ← map_mul, ← AlgEquiv.mul_apply, ← map_mul]
  congr 2
  change (basisChange K)⁻¹ * (basisChange K * ReducedGraphAction.matrixRepresentation K w * (basisChange K)⁻¹) =
    ReducedGraphAction.matrixRepresentation K w * (basisChange K)⁻¹
  group

/-- In these actual coordinates the odd generator is the literal two-block swap. -/
theorem matrixRepresentation_odd (z : DualMixed K) :
    (matrixRepresentation K (SemidirectProduct.inr M9.CentralSignQuotient.epsilon)).val.mulVec
      (actualCoordinates K z) =
        GraphGrassmannianChart.ambientCoordinates ((traceSplit K) z.2,(conicSplit K) z.1) := by
  rw [matrixRepresentation_actual, dualSemidirectRepresentation_inr_epsilon]
  change GraphGrassmannianChart.ambientCoordinates
    ((conicSplit K) ((M9.PrimitiveBlockCoordinates.symmetricDualEquiv K).symm z.2),
      (traceSplit K) (M9.PrimitiveBlockCoordinates.symmetricDualEquiv K z.1)) = _
  rw [traceSplit, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

theorem actualCoordinates_scale (s t : K) (z : DualMixed K) :
    actualCoordinates K (s • z.1,t • z.2) =
      (Matrix.diagonal (GraphCentralMatrices.ambientWeights s t)).mulVec (actualCoordinates K z) := by
  change GraphGrassmannianChart.ambientCoordinates ((conicSplit K) (s • z.1),(traceSplit K) (t • z.2)) =
    (Matrix.diagonal (GraphCentralMatrices.ambientWeights s t)).mulVec
      (GraphGrassmannianChart.ambientCoordinates ((conicSplit K) z.1,(traceSplit K) z.2))
  rw [GraphCentralMatrices.diagonal_mulVec_ambient, map_smul, map_smul]

theorem matrixRepresentation_center_diagonal (a : K) (ha : a^3 = 1) :
    (matrixRepresentation K (SemidirectProduct.inl
      (M9.PrimitiveRepresentation.centralElement K a ha))).val =
      Matrix.diagonal (GraphCentralMatrices.ambientWeights (a^2) ((a⁻¹)^2)) := by
  apply Matrix.ext_of_mulVec_single
  intro j
  let z := (actualCoordinates K).symm (Pi.single j 1)
  have h := matrixRepresentation_actual K
    (SemidirectProduct.inl (M9.PrimitiveRepresentation.centralElement K a ha)) z
  rw [ReducedGraphAction.dualSemidirectRepresentation_center, actualCoordinates_scale] at h
  simpa only [z, LinearEquiv.apply_symm_apply] using h

theorem nativeField_center_eq (a : ReducedGraphCenter.Roots) :
    nativeFieldRepresentation ℂ (ReducedGraphCenter.centralElement a) =
      ReducedGraphAction.nativeFieldRepresentation ℂ (ReducedGraphCenter.centralElement a) := by
  have hm : matrixRepresentation ℂ (ReducedGraphCenter.centralElement a) =
      ReducedGraphAction.matrixRepresentation ℂ (ReducedGraphCenter.centralElement a) := by
    apply Units.ext
    rw [ReducedGraphCenter.centralElement, matrixRepresentation_center_diagonal,
      GraphCentralMatrices.matrixRepresentation_center_diagonal]
  change GraphGrassmannianLinearAction.fieldRepresentation ℂ
    (matrixRepresentation ℂ (ReducedGraphCenter.centralElement a)) =
      GraphGrassmannianLinearAction.fieldRepresentation ℂ
        (ReducedGraphAction.matrixRepresentation ℂ (ReducedGraphCenter.centralElement a))
  rw [hm]

/-- Canonical-chart invariants are still invariants of an actual native scheme action. -/
def canonicalFixedField : IntermediateField ℂ (GrassmannianCharts.space ℂ 4 12).functionField :=
  IntermediateField.fixedField (nativeFieldRepresentation ℂ).range

/-- The literal native ambient basis change identifies its true fixed field
with the original true reduced-space fixed field. -/
def basisFixedEquiv : canonicalFixedField ≃ₐ[ℂ] ReducedGraphTwistedAction.nativeHFixedField where
  toFun z := ⟨basisField ℂ z.val, by
    apply (ReducedGraphTwistedAction.mem_nativeHFixedField_iff _).mpr
    intro w
    rw [← basisField_equivariance]
    exact congrArg (basisField ℂ)
      ((ReducedGraphTwistedAction.mem_fixedField_range_iff (nativeFieldRepresentation ℂ) z.val).mp z.property w)⟩
  invFun z := ⟨(basisField ℂ).symm z.val, by
    apply (ReducedGraphTwistedAction.mem_fixedField_range_iff (nativeFieldRepresentation ℂ) _).mpr
    intro w
    apply (basisField ℂ).injective
    rw [basisField_equivariance, AlgEquiv.apply_symm_apply]
    exact (ReducedGraphTwistedAction.mem_nativeHFixedField_iff z.val).mp z.property w⟩
  left_inv z := Subtype.ext ((basisField ℂ).symm_apply_apply z.val)
  right_inv z := Subtype.ext ((basisField ℂ).apply_symm_apply z.val)
  map_mul' z v := Subtype.ext (map_mul (basisField ℂ) z.val v.val)
  map_add' z v := Subtype.ext (map_add (basisField ℂ) z.val v.val)
  commutes' c := Subtype.ext ((basisField ℂ).commutes c)

end M9Native.ConicCompatibleGraphCoordinates
