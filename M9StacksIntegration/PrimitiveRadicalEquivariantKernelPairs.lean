module

public import M9StacksIntegration.PrimitiveReducedFieldMatrixAction
public import M9StacksIntegration.PrimitiveConstantOriginalExtension

@[expose] public section

/-! Actual symplectically related native family points give actual reduced
stabilizer relations. This is the equivariant kernel-pair geometry needed
in addition to the equal-image kernel pair. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory Module
open scoped Classical Matrix

namespace M9Native.PrimitiveRadicalEquivariantKernelPairs
open M9.ExteriorPrimitive M9.PrimitiveStabilizer M9.PrimitiveRadicalFiber
open M9.PrimitiveBlockCoordinates M9.PrimitiveTwistedReduced
open PrimitiveRadicalOrbitPoints PrimitiveRadicalOrbitKernelPoints
open PrimitiveRhoFiberNondegenerate PrimitiveRhoFiberReducedCoordinates

variable (K : Type) [Field K] [Algebra ℂ K]
local instance extensionCharZero : CharZero K := PrimitiveExtensionFieldBridge.charZero_extension K
local instance primitiveGroup : AddCommGroup (Primitive K) :=
  { (Primitive K).addCommGroup with toAddCommMonoid := (Primitive K).addCommMonoid }
local instance perpGroup : AddCommGroup (Perp K) :=
  { (Perp K).addCommGroup with toAddCommMonoid := (Perp K).addCommMonoid }

theorem fieldPoint_coordinates (f : nondegenerateRing →ₐ[ℂ] K) :
    (((rhoFiberEquiv K (PrimitiveRadicalKernelPair.fieldPoint K f)).val).map
      (reducedDualEquiv K).toLinearMap).map
        (ReducedGraphAction.actualCoordinates K).toLinearMap =
      (Matrix.toLin' (localizedGraph.map f)).range := by
  rw [← Submodule.map_comp]
  exact rhoFiberEquiv_fieldPoint_coordinates K f

/-- An original symplectic collision in the actual rho fiber determines the
literal original reduced graph relation, with its actual semidirect element. -/
theorem exists_graph_relation_of_fiber_collision (g g' : Sp6 K)
    (f f' : nondegenerateRing →ₐ[ℂ] K)
    (h : planeAction K g (PrimitiveRadicalKernelPair.fieldPoint K f).val =
      planeAction K g' (PrimitiveRadicalKernelPair.fieldPoint K f').val) :
    ∃ w : ReducedGraphAction.Stabilizer K,
      (Matrix.toLin' (localizedGraph.map f')).range =
        ((Matrix.toLin' (localizedGraph.map f)).range).map
          (Matrix.toLin' (ReducedGraphAction.matrixRepresentation K w).val) := by
  let c := PrimitiveRadicalKernelPair.collisionStabilizer K g g'
    (PrimitiveRadicalKernelPair.fieldPoint K f) (PrimitiveRadicalKernelPair.fieldPoint K f') h
  let w := M9.PrimitiveProjectiveStabilizer.toProjectiveSemidirect K
    (PrimitiveRadicalKernelPair.imaginaryUnit K) (PrimitiveRadicalKernelPair.imaginaryUnit_sq K) c
  refine ⟨w,?_⟩
  have hr := PrimitiveRadicalKernelPair.collision_reduced_fourPlane K g g'
    (PrimitiveRadicalKernelPair.fieldPoint K f) (PrimitiveRadicalKernelPair.fieldPoint K f') h
  calc
    (Matrix.toLin' (localizedGraph.map f')).range =
        (((rhoFiberEquiv K (PrimitiveRadicalKernelPair.fieldPoint K f')).val).map
          (reducedDualEquiv K).toLinearMap).map
            (ReducedGraphAction.actualCoordinates K).toLinearMap := (fieldPoint_coordinates K f').symm
    _ = ((((rhoFiberEquiv K (PrimitiveRadicalKernelPair.fieldPoint K f)).val).map
          (reducedDualEquiv K).toLinearMap).map (dualSemidirectRepresentation K w)).map
            (ReducedGraphAction.actualCoordinates K).toLinearMap :=
      congrArg (fun U : Submodule K (DualMixed K) =>
        U.map (ReducedGraphAction.actualCoordinates K).toLinearMap) hr
    _ = _ := (PrimitiveRadicalOrbitReducedPoints.actualCoordinates_map K w _).trans
      (congrArg (fun U : Submodule K (Fin 12 → K) =>
        U.map (Matrix.toLin' (ReducedGraphAction.matrixRepresentation K w).val))
          (fieldPoint_coordinates K f))

/-- The original primitive-kernel transport follows from the genuine native
action equality and genuine matrix quotient classes. -/
theorem kernel_transport_of_native_action (g : Sp6 K) (y z : Point K)
    (h : PrimitiveFieldMatrixAction.actPoint K g (nativePoint K y) (nativePoint_projection K y) =
      nativePoint K z) :
    kernelAt K z = (kernelAt K y).map (primitiveLinear K g).toLinearMap := by
  have hb : PrimitiveFieldMatrixAction.actPoint K g (nativePoint K y) (nativePoint_projection K y) ≫
      PrimitiveGrassmannianAction.projection = nativePoint K z ≫ PrimitiveGrassmannianAction.projection := by
    rw [PrimitiveFieldMatrixAction.actPoint_projection,nativePoint_projection]
  have hq := (GrassmannianFieldKernels.points_eq_iff_kernel_eq (K := K) (k := 9) (n := 14)
    (PrimitiveFieldMatrixAction.actPoint K g (nativePoint K y) (nativePoint_projection K y))
    (nativePoint K z) (quotientAt K y * PrimitiveFieldMatrixAction.coordinateMatrix K g⁻¹)
    (quotientAt K z) (PrimitiveFieldMatrixAction.acted_surjective K g _ (quotientAt_surjective K y))
    (quotientAt_surjective K z)
    (PrimitiveFieldMatrixAction.actPoint_class K g _ (nativePoint_projection K y) _
      (quotientAt_surjective K y) (nativePoint_class K y)) (nativePoint_class K z) hb).mp h
  have hm := congrArg (fun U : Submodule K (Fin 14 → K) =>
    U.map (PrimitiveExtensionFieldBridge.fieldCoordinates K).symm.toLinearMap) hq
  change (Matrix.toLin' (quotientAt K y * PrimitiveFieldMatrixAction.coordinateMatrix K g⁻¹)).ker.map
    (PrimitiveExtensionFieldBridge.fieldCoordinates K).symm.toLinearMap = kernelAt K z at hm
  rw [PrimitiveFieldMatrixAction.actedKernel_original] at hm
  exact hm.symm

/-- Any genuine native group-action relation of source-family points gives
the actual reduced stabilizer relation, without a section or orbit-lifting premise. -/
theorem exists_reduced_relation_of_native_action (g : Sp6 K) (y z : Point K)
    (h : PrimitiveFieldMatrixAction.actPoint K g (nativePoint K y) (nativePoint_projection K y) =
      nativePoint K z) :
    ∃ w : ReducedGraphAction.Stabilizer K,
      PrimitiveReducedFieldMatrixAction.fieldAction K (ReducedGraphAction.matrixRepresentation K w)⁻¹
        (PrimitiveRhoGraphNativePoints.point K (rightPoint K y)) =
      PrimitiveRhoGraphNativePoints.point K (rightPoint K z) := by
  have hk := kernel_transport_of_native_action K g y z h
  have hp : planeAction K (g * originalGroupAt K y)
      (PrimitiveRadicalKernelPair.fieldPoint K (rightPoint K y)).val =
    planeAction K (originalGroupAt K z)
      (PrimitiveRadicalKernelPair.fieldPoint K (rightPoint K z)).val := by
    rw [PrimitiveRadicalKernelPair.planeAction_mul]
    apply Subtype.ext
    change (planeAt K y).val.map (primitiveLinear K g).toLinearMap = (planeAt K z).val
    rw [← kernelAt_eq_planeAt,← kernelAt_eq_planeAt]
    exact hk.symm
  obtain ⟨w,hw⟩ := exists_graph_relation_of_fiber_collision K (g * originalGroupAt K y)
    (originalGroupAt K z) (rightPoint K y) (rightPoint K z) hp
  exact ⟨w,PrimitiveReducedFieldMatrixAction.fieldAction_graph_points K
    (ReducedGraphAction.matrixRepresentation K w) _ _ hw⟩

/-- Surjectivity follows from the actual central-sign quotient equivalence,
not from an assumed stabilizer-lifting property. -/
theorem toProjectiveSemidirect_surjective : Function.Surjective
    (M9.PrimitiveProjectiveStabilizer.toProjectiveSemidirect K
      (PrimitiveRadicalKernelPair.imaginaryUnit K) (PrimitiveRadicalKernelPair.imaginaryUnit_sq K)) :=
  (M9.PrimitiveProjectiveStabilizer.stabilizerQuotientEquiv K
    (PrimitiveRadicalKernelPair.imaginaryUnit K) (PrimitiveRadicalKernelPair.imaginaryUnit_sq K)).surjective.comp
      (QuotientGroup.mk'_surjective (M9.PrimitiveProjectiveStabilizer.centralSignSubgroup K))

theorem map_reducedCoordinates (V : Submodule K (Reduced K)) :
    (V.map (reducedDualEquiv K).toLinearMap).map
      (ReducedGraphAction.actualCoordinates K).toLinearMap =
        V.map (reducedCoordinates K).toLinearMap := by
  rw [← Submodule.map_comp]
  rfl

def fiberCoordinates (U : RhoFiber K) : Submodule K (Fin 12 → K) :=
  (rhoFiberEquiv K U).val.map (reducedCoordinates K).toLinearMap

theorem fiberCoordinates_injective : Function.Injective (fiberCoordinates K) := by
  intro U W h
  apply (rhoFiberEquiv K).injective
  apply Subtype.ext
  apply Submodule.map_injective_of_injective
    (f := (reducedCoordinates K).toLinearMap) (reducedCoordinates K).injective
  exact h

theorem fiberCoordinates_fieldPoint (f : nondegenerateRing →ₐ[ℂ] K) :
    fiberCoordinates K (PrimitiveRadicalKernelPair.fieldPoint K f) =
      (Matrix.toLin' (localizedGraph.map f)).range :=
  rhoFiberEquiv_fieldPoint_coordinates K f

theorem fiberCoordinates_action (c : lineStabilizer K) (U : RhoFiber K) :
    fiberCoordinates K (stabilizerFiberMap K c U) =
      (fiberCoordinates K U).map
        (Matrix.toLin' (ReducedGraphAction.matrixRepresentation K
          (M9.PrimitiveProjectiveStabilizer.toProjectiveSemidirect K
            (PrimitiveRadicalKernelPair.imaginaryUnit K) (PrimitiveRadicalKernelPair.imaginaryUnit_sq K) c)).val) := by
  let w := M9.PrimitiveProjectiveStabilizer.toProjectiveSemidirect K
    (PrimitiveRadicalKernelPair.imaginaryUnit K) (PrimitiveRadicalKernelPair.imaginaryUnit_sq K) c
  let V : Submodule K (Reduced K) := (rhoFiberEquiv K U).val
  let V' : Submodule K (Reduced K) := (rhoFiberEquiv K (stabilizerFiberMap K c U)).val
  have hr : V'.map (reducedDualEquiv K).toLinearMap =
      (V.map (reducedDualEquiv K).toLinearMap).map (dualSemidirectRepresentation K w) :=
    rhoFiberEquiv_dual_semidirect_action K (PrimitiveRadicalKernelPair.imaginaryUnit K)
      (PrimitiveRadicalKernelPair.imaginaryUnit_sq K) c U
  have hm := congrArg (fun T : Submodule K (DualMixed K) =>
    T.map (ReducedGraphAction.actualCoordinates K).toLinearMap) hr
  have ha := PrimitiveRadicalOrbitReducedPoints.actualCoordinates_map K w
    (V.map (reducedDualEquiv K).toLinearMap)
  have hc := congrArg (fun T : Submodule K (Fin 12 → K) =>
    T.map (Matrix.toLin' (ReducedGraphAction.matrixRepresentation K w).val)) (map_reducedCoordinates K V)
  exact (map_reducedCoordinates K V').symm.trans (hm.trans (ha.trans hc))

/-- A literal stabilizer relation of the reduced graphs lifts to an actual
native symplectic action between the original nine-plane family points. -/
theorem exists_native_action_of_graph_relation (w : ReducedGraphAction.Stabilizer K) (y z : Point K)
    (h : (Matrix.toLin' (graphAt K z)).range =
      ((Matrix.toLin' (graphAt K y)).range).map
        (Matrix.toLin' (ReducedGraphAction.matrixRepresentation K w).val)) :
    ∃ g : Sp6 K,
      PrimitiveFieldMatrixAction.actPoint K g (nativePoint K y) (nativePoint_projection K y) =
        nativePoint K z := by
  obtain ⟨c,hc⟩ := toProjectiveSemidirect_surjective K w
  let U := PrimitiveRadicalKernelPair.fieldPoint K (rightPoint K y)
  let W := PrimitiveRadicalKernelPair.fieldPoint K (rightPoint K z)
  have hU : stabilizerFiberMap K c U = W := by
    apply fiberCoordinates_injective K
    have ha := fiberCoordinates_action K c U
    rw [hc] at ha
    have hy : fiberCoordinates K U = (Matrix.toLin' (graphAt K y)).range :=
      fiberCoordinates_fieldPoint K (rightPoint K y)
    have hz : fiberCoordinates K W = (Matrix.toLin' (graphAt K z)).range :=
      fiberCoordinates_fieldPoint K (rightPoint K z)
    have hm := congrArg (fun T : Submodule K (Fin 12 → K) =>
      T.map (Matrix.toLin' (ReducedGraphAction.matrixRepresentation K w).val)) hy
    exact ha.trans (hm.trans (h.symm.trans hz.symm))
  have hcU : planeAction K c.val U.val = W.val := congrArg (fun V : RhoFiber K => V.val) hU
  let g := originalGroupAt K z * c.val * (originalGroupAt K y)⁻¹
  have hp : planeAt K z = planeAction K g (planeAt K y) := by
    change planeAction K (originalGroupAt K z) W.val =
      planeAction K (originalGroupAt K z * c.val * (originalGroupAt K y)⁻¹)
        (planeAction K (originalGroupAt K y) U.val)
    rw [← PrimitiveRadicalKernelPair.planeAction_mul,mul_assoc,inv_mul_cancel,mul_one,
      PrimitiveRadicalKernelPair.planeAction_mul,hcU]
  have hk : kernelAt K z = (kernelAt K y).map (primitiveLinear K g).toLinearMap := by
    rw [kernelAt_eq_planeAt,kernelAt_eq_planeAt]
    exact congrArg (fun V : RankEightNinePlanes K => V.val) hp
  exact ⟨g,PrimitiveFieldMatrixAction.actPoint_eq_of_original_kernel_transport K g
    (nativePoint K y) (nativePoint K z) (nativePoint_projection K y) (nativePoint_projection K z)
    (quotientAt K y) (quotientAt K z) (quotientAt_surjective K y) (quotientAt_surjective K z)
    (nativePoint_class K y) (nativePoint_class K z) hk⟩

end M9Native.PrimitiveRadicalEquivariantKernelPairs
