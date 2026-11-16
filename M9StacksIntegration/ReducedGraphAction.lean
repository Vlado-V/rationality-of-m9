module

public import M9StacksIntegration.GraphGrassmannianLinearAction
public import M9StacksIntegration.GraphGrassmannianChart
public import M9.PrimitiveTwistedReduced

/-! The actual stabilizer SL3 semidirect C2 acts on the genuine native Gr4(12)
through its proved representation on Sym²(K³) plus the actual dual. No quotient
by the cubic center is introduced here. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix

universe u

namespace M9Native.ReducedGraphAction

open M9.PrimitiveTwistedReduced M9.GraphBundleDescent

variable (K : Type u) [Field K] [CharZero K]

abbrev Stabilizer := M9.PrimitiveProjectiveStabilizer.specialLinearSemidirect K
abbrev space := GrassmannianCharts.space K 4 12
abbrev CoordinateSpace := Fin 12 → K

/-- Coordinates retain the actual symmetric-matrix space and its actual dual,
with the same splitting used in the proved native graph chart. -/
def actualCoordinates : DualMixed K ≃ₗ[K] CoordinateSpace K :=
  ((symmetricSplit K).prodCongr (dualSymmetricSplit K)).trans
    GraphGrassmannianChart.ambientCoordinates

/-- An honest linear-automorphism representation, conjugate to the proved
actual reduced primitive representation. -/
def dualLinearRepresentation : Stabilizer K →* (DualMixed K ≃ₗ[K] DualMixed K) where
  toFun w := (mixedDualEquiv K).symm.trans
    ((mixedSemidirectLinearRepresentation K w).trans (mixedDualEquiv K))
  map_one' := by
    apply LinearEquiv.ext
    intro z
    change mixedDualEquiv K (mixedSemidirectLinearRepresentation K 1 ((mixedDualEquiv K).symm z)) = z
    rw [map_one]
    exact (mixedDualEquiv K).apply_symm_apply z
  map_mul' w v := by
    apply LinearEquiv.ext
    intro z
    change mixedDualEquiv K (mixedSemidirectLinearRepresentation K (w * v) ((mixedDualEquiv K).symm z)) =
      mixedDualEquiv K (mixedSemidirectLinearRepresentation K w
        ((mixedDualEquiv K).symm (mixedDualEquiv K
          (mixedSemidirectLinearRepresentation K v ((mixedDualEquiv K).symm z)))))
    rw [map_mul, LinearEquiv.symm_apply_apply]
    rfl

theorem dualLinearRepresentation_apply (w : Stabilizer K) (z : DualMixed K) :
    dualLinearRepresentation K w z = dualSemidirectRepresentation K w z := rfl

def coordinateRepresentation : Stabilizer K →* (CoordinateSpace K ≃ₗ[K] CoordinateSpace K) where
  toFun w := (actualCoordinates K).symm.trans
    ((dualLinearRepresentation K w).trans (actualCoordinates K))
  map_one' := by ext z; simp
  map_mul' w v := by ext z; simp

def coordinateGL : (CoordinateSpace K ≃ₗ[K] CoordinateSpace K) ≃*
    Matrix.GeneralLinearGroup (Fin 12) K :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (CoordinateSpace K)).symm.trans
    Matrix.GeneralLinearGroup.toLin.symm

def matrixRepresentation : Stabilizer K →* Matrix.GeneralLinearGroup (Fin 12) K :=
  (coordinateGL K).toMonoidHom.comp (coordinateRepresentation K)

omit [CharZero K] in
theorem coordinateGL_mulVec (e : CoordinateSpace K ≃ₗ[K] CoordinateSpace K)
    (v : CoordinateSpace K) : (coordinateGL K e).val.mulVec v = e v := by
  have h := Matrix.GeneralLinearGroup.toLin.apply_symm_apply
    (LinearMap.GeneralLinearGroup.ofLinearEquiv e)
  exact congrArg (fun f : LinearMap.GeneralLinearGroup K (CoordinateSpace K) =>
    (f : Module.End K (CoordinateSpace K)) v) h

theorem matrixRepresentation_actual (w : Stabilizer K) (z : DualMixed K) :
    (matrixRepresentation K w).val.mulVec (actualCoordinates K z) =
      actualCoordinates K (dualSemidirectRepresentation K w z) := by
  change (coordinateGL K (coordinateRepresentation K w)).val.mulVec (actualCoordinates K z) = _
  rw [coordinateGL_mulVec]
  change actualCoordinates K (dualLinearRepresentation K w
    ((actualCoordinates K).symm (actualCoordinates K z))) = _
  rw [LinearEquiv.symm_apply_apply, dualLinearRepresentation_apply]

/-- The actual native quotient-functor action of the full stabilizer. -/
def nativeAction (w : Stabilizer K) : space K ⟶ space K :=
  GraphGrassmannianLinearAction.action K (matrixRepresentation K w)

@[reassoc] theorem nativeAction_projection (w : Stabilizer K) :
    nativeAction K w ≫ GrassmannianCharts.projection K 4 12 =
      GrassmannianCharts.projection K 4 12 :=
  GraphGrassmannianLinearAction.action_projection K _

theorem nativeAction_one : nativeAction K 1 = 𝟙 (space K) := by
  rw [nativeAction, map_one, GraphGrassmannianLinearAction.action_one]

theorem nativeAction_mul (w v : Stabilizer K) :
    nativeAction K w ≫ nativeAction K v = nativeAction K (w * v) := by
  simp only [nativeAction, map_mul, GraphGrassmannianLinearAction.action_mul]

instance nativeAction_isIso (w : Stabilizer K) : IsIso (nativeAction K w) := by
  unfold nativeAction
  infer_instance

instance nativeAction_isDominant (w : Stabilizer K) : IsDominant (nativeAction K w) := by
  unfold nativeAction
  infer_instance

def nativeFieldRepresentation : Stabilizer K →*
    ((space K).functionField ≃ₐ[K] (space K).functionField) :=
  (GraphGrassmannianLinearAction.fieldRepresentation K).comp (matrixRepresentation K)

theorem nativeFieldRepresentation_eq_map (w : Stabilizer K) :
    (nativeFieldRepresentation K w).toRingHom = NativeDominantFunctionField.map (nativeAction K w) :=
  GraphGrassmannianLinearAction.fieldAutomorphism_eq_map K _

/-- Every actual test-scheme quotient is transformed by the actual stabilizer matrix. -/
theorem nativeAction_classifier {T : Scheme.{u}} (p : T ⟶ space K) (w : Stabilizer K) :
    GraphGrassmannianLinearAction.pointClass K (p ≫ nativeAction K w) =
      GraphGrassmannianLinearAction.transformPoints K
        (p ≫ GrassmannianCharts.projection K 4 12) (matrixRepresentation K w)
        (GraphGrassmannianLinearAction.pointClass K p) :=
  GraphGrassmannianLinearAction.pointClass_action K p _

/-- On the connected subgroup this is the proved actual Q plus dual-Q action. -/
theorem matrixRepresentation_connected (g : Matrix.SpecialLinearGroup (Fin 3) K) (z : DualMixed K) :
    (matrixRepresentation K (SemidirectProduct.inl g)).val.mulVec (actualCoordinates K z) =
      actualCoordinates K (M9.PrimitiveBlockCoordinates.dualMixedAction K g z) := by
  rw [matrixRepresentation_actual, dualSemidirectRepresentation_inl]

/-- The odd generator uses the actual trace duality in both directions. -/
theorem matrixRepresentation_odd (z : DualMixed K) :
    (matrixRepresentation K (SemidirectProduct.inr M9.CentralSignQuotient.epsilon)).val.mulVec
        (actualCoordinates K z) =
      actualCoordinates K ((M9.PrimitiveBlockCoordinates.symmetricDualEquiv K).symm z.2,
        M9.PrimitiveBlockCoordinates.symmetricDualEquiv K z.1) := by
  rw [matrixRepresentation_actual, dualSemidirectRepresentation_inr_epsilon]

/-- The genuine cubic center retains its two nontrivial actual weights. -/
theorem dualSemidirectRepresentation_center (a : K) (ha : a ^ 3 = 1) (z : DualMixed K) :
    dualSemidirectRepresentation K
        (SemidirectProduct.inl (M9.PrimitiveRepresentation.centralElement K a ha)) z =
      (a ^ 2 • z.1, (a⁻¹) ^ 2 • z.2) := by
  obtain ⟨w, rfl⟩ := (mixedDualEquiv K).surjective z
  rw [dualSemidirectRepresentation_apply, LinearEquiv.symm_apply_apply,
    mixedSemidirectRepresentation_inl]
  have hm := congrArg (fun r : M9.PrimitiveRepresentation.Coordinates K => (r.2.1,r.2.2.1))
    (M9.PrimitiveRepresentation.sl3Action_centralElement K a ha 0 0 w.1 w.2)
  change M9.PrimitiveBlockCoordinates.mixedAction K
    (M9.PrimitiveRepresentation.centralElement K a ha) w = (a^2 • w.1,(a⁻¹)^2 • w.2) at hm
  rw [hm]
  change (a^2 • w.1,M9.PrimitiveBlockCoordinates.symmetricDualEquiv K ((a⁻¹)^2 • w.2)) =
    (a^2 • w.1,(a⁻¹)^2 • M9.PrimitiveBlockCoordinates.symmetricDualEquiv K w.2)
  rw [map_smul]

theorem matrixRepresentation_center (a : K) (ha : a ^ 3 = 1) (z : DualMixed K) :
    (matrixRepresentation K
      (SemidirectProduct.inl (M9.PrimitiveRepresentation.centralElement K a ha))).val.mulVec
        (actualCoordinates K z) = actualCoordinates K (a^2 • z.1,(a⁻¹)^2 • z.2) := by
  rw [matrixRepresentation_actual, dualSemidirectRepresentation_center]

end M9Native.ReducedGraphAction
