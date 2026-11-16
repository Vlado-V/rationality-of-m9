module

public import M9StacksIntegration.PrimitiveRadicalOrbitKernelPoints
public import M9StacksIntegration.PrimitiveRhoFiberReducedCoordinates

/-! Native orbit-family collisions in the literal original reduced graph coordinates. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module
open scoped Classical Matrix

namespace M9Native.PrimitiveRadicalOrbitReducedPoints
open M9.ExteriorPrimitive M9.PrimitiveStabilizer M9.PrimitiveRadicalFiber
open M9.PrimitiveBlockCoordinates M9.PrimitiveTwistedReduced
open PrimitiveRadicalOrbitPoints PrimitiveRadicalOrbitKernelPoints
open PrimitiveRhoFiberReducedCoordinates

variable (K : Type) [Field K] [Algebra ℂ K]
local instance extensionCharZero : CharZero K := PrimitiveExtensionFieldBridge.charZero_extension K
local instance primitiveGroup : AddCommGroup (Primitive K) :=
  { (Primitive K).addCommGroup with toAddCommMonoid := (Primitive K).addCommMonoid }
local instance perpGroup : AddCommGroup (Perp K) :=
  { (Perp K).addCommGroup with toAddCommMonoid := (Perp K).addCommMonoid }

/-- This is the actual semidirect element obtained from the actual relative
symplectic transformation of a native collision. -/
def collisionReducedElement (y z : Point K) (h : nativePoint K y = nativePoint K z) :
    ReducedGraphAction.Stabilizer K :=
  M9.PrimitiveProjectiveStabilizer.toProjectiveSemidirect K
    (PrimitiveRadicalKernelPair.imaginaryUnit K) (PrimitiveRadicalKernelPair.imaginaryUnit_sq K)
    (collisionStabilizerAt K y z h)

/-- The literal coordinate matrix intertwines the original dual mixed action
on every actual subspace, including the cubic center. -/
theorem actualCoordinates_map (w : ReducedGraphAction.Stabilizer K)
    (U : Submodule K (DualMixed K)) :
    (U.map (dualSemidirectRepresentation K w)).map
        (ReducedGraphAction.actualCoordinates K).toLinearMap =
      (U.map (ReducedGraphAction.actualCoordinates K).toLinearMap).map
        (Matrix.toLin' (ReducedGraphAction.matrixRepresentation K w).val) := by
  rw [← Submodule.map_comp,← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro v
  exact (ReducedGraphAction.matrixRepresentation_actual K w v).symm

/-- The original graph columns, with their original order and normalization,
are the coordinates of the intrinsic reduced four-plane at every source point. -/
theorem reducedPlane_graphAt (y : Point K) :
    (((rhoFiberEquiv K (PrimitiveRadicalKernelPair.fieldPoint K (rightPoint K y))).val).map
      (reducedDualEquiv K).toLinearMap).map
        (ReducedGraphAction.actualCoordinates K).toLinearMap =
      (Matrix.toLin' (graphAt K y)).range := by
  rw [← Submodule.map_comp]
  exact rhoFiberEquiv_fieldPoint_coordinates K (rightPoint K y)

/-- Equality of the actual native nine-plane images gives the genuine actual
SL3 semidirect C2 relation between the literal original graph four-planes.
No extension-field invariance of rational functions is asserted here. -/
theorem collision_graph_ranges (y z : Point K) (h : nativePoint K y = nativePoint K z) :
    (Matrix.toLin' (graphAt K z)).range =
      ((Matrix.toLin' (graphAt K y)).range).map
        (Matrix.toLin' (ReducedGraphAction.matrixRepresentation K
          (collisionReducedElement K y z h)).val) := by
  calc
    (Matrix.toLin' (graphAt K z)).range =
        (((rhoFiberEquiv K (PrimitiveRadicalKernelPair.fieldPoint K (rightPoint K z))).val).map
          (reducedDualEquiv K).toLinearMap).map
            (ReducedGraphAction.actualCoordinates K).toLinearMap :=
      (reducedPlane_graphAt K z).symm
    _ = ((((rhoFiberEquiv K (PrimitiveRadicalKernelPair.fieldPoint K (rightPoint K y))).val).map
          (reducedDualEquiv K).toLinearMap).map
            (dualSemidirectRepresentation K (collisionReducedElement K y z h))).map
              (ReducedGraphAction.actualCoordinates K).toLinearMap :=
      congrArg (fun U : Submodule K (DualMixed K) =>
        U.map (ReducedGraphAction.actualCoordinates K).toLinearMap)
          (collision_reduced_fourPlane K y z h)
    _ = _ := (actualCoordinates_map K (collisionReducedElement K y z h) _).trans
      (congrArg (fun U : Submodule K (Fin 12 → K) => U.map
        (Matrix.toLin' (ReducedGraphAction.matrixRepresentation K
          (collisionReducedElement K y z h)).val)) (reducedPlane_graphAt K y))

end M9Native.PrimitiveRadicalOrbitReducedPoints
