module

public import M9StacksIntegration.PrimitiveRhoFiberFieldPoints
public import M9.PrimitiveRadicalReducedAction

/-!
# Actual radical orbit-family collisions over extension fields

The intrinsic radical forces the relative symplectic transformation of
any two actual fiber points with the same orbit image into the actual
rho-line stabilizer. Its induced action is the proved SL3 semidirect C2
action on the actual reduced four-plane, with no stabilizer premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module
open scoped Classical

namespace M9Native.PrimitiveRadicalKernelPair
open M9.ExteriorPrimitive M9.PrimitiveStabilizer M9.PrimitiveRadicalFiber
open M9.PrimitiveBlockCoordinates M9.PrimitiveTwistedReduced
open PrimitiveRhoFiberFieldPoints PrimitiveRhoFiberNondegenerate PrimitiveExtensionFieldBridge

variable (K : Type) [Field K] [Algebra ℂ K]
local instance extensionCharZero : CharZero K := charZero_extension K
local instance primitiveGroup : AddCommGroup (Primitive K) :=
  { (Primitive K).addCommGroup with toAddCommMonoid := (Primitive K).addCommMonoid }
local instance perpGroup : AddCommGroup (Perp K) :=
  { (Perp K).addCommGroup with toAddCommMonoid := (Perp K).addCommMonoid }

/-- Actual rho-fiber point supplied by the proved literal matrix radical, over every extension field. -/
def rhoFiberPoint (P : Matrix (Fin 12) (Fin 4) K) (hP : (gramMatrix K P).det ≠ 0) : RhoFiber K :=
  (M9.RadicalMap.pointFiberEquiv (primitivePairing K) (rhoProjective K)).symm
    ⟨quotientKernel K P,(quotientKernel_finrank_radical K P hP).1,by
      simpa only [rhoProjective,Projectivization.submodule_mk,rhoLine] using
        (quotientKernel_finrank_radical K P hP).2⟩

theorem rhoFiberPoint_submodule (P : Matrix (Fin 12) (Fin 4) K)
    (hP : (gramMatrix K P).det ≠ 0) : (rhoFiberPoint K P hP).val.val = quotientKernel K P := rfl

def fieldPoint (f : nondegenerateRing →ₐ[ℂ] K) : RhoFiber K :=
  rhoFiberPoint K (localizedGraph.map f) (fieldPoint_gram_det_ne_zero f)

theorem planeAction_one (U : RankEightNinePlanes K) : planeAction K 1 U = U := by
  apply Subtype.ext
  change U.val.map (primitiveLinear K 1).toLinearMap = U.val
  have h : (primitiveLinear K 1).toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun (primitiveAction_one K) x
  rw [h,Submodule.map_id]

theorem planeAction_mul (g h : Sp6 K) (U : RankEightNinePlanes K) :
    planeAction K (g*h) U = planeAction K g (planeAction K h U) := by
  apply Subtype.ext
  change U.val.map (primitiveLinear K (g*h)).toLinearMap =
    (U.val.map (primitiveLinear K h).toLinearMap).map (primitiveLinear K g).toLinearMap
  rw [← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (primitiveAction_mul K g h) x

/-- A collision in the actual symplectic orbit-family fixes the original radical line. -/
theorem relative_transformation_stabilizes (g g' : Sp6 K) (U W : RhoFiber K)
    (h : planeAction K g U.val = planeAction K g' W.val) :
    projectiveAction K (g'⁻¹*g) (rhoProjective K) = rhoProjective K := by
  have hW : planeAction K (g'⁻¹*g) U.val = W.val := by
    rw [planeAction_mul,h,← planeAction_mul,inv_mul_cancel,planeAction_one]
  have hr := congrArg (radicalLineMap K) hW
  rw [radicalLineMap_equivariant,U.property] at hr
  change projectiveAction K (g'⁻¹*g) (rhoProjective K) = radicalLineMap K W.val at hr
  rw [W.property] at hr
  exact hr

/-- The stabilizer element is constructed from the actual collision, rather than assumed. -/
def collisionStabilizer (g g' : Sp6 K) (U W : RhoFiber K)
    (h : planeAction K g U.val = planeAction K g' W.val) : lineStabilizer K :=
  ⟨g'⁻¹*g,relative_transformation_stabilizes K g g' U W h⟩

theorem collisionStabilizer_val (g g' : Sp6 K) (U W : RhoFiber K)
    (h : planeAction K g U.val = planeAction K g' W.val) :
    (collisionStabilizer K g g' U W h).val = g'⁻¹*g := rfl

theorem collision_fiber_transport (g g' : Sp6 K) (U W : RhoFiber K)
    (h : planeAction K g U.val = planeAction K g' W.val) :
    stabilizerFiberMap K (collisionStabilizer K g g' U W h) U = W := by
  apply Subtype.ext
  change planeAction K (g'⁻¹*g) U.val = W.val
  rw [planeAction_mul,h,← planeAction_mul,inv_mul_cancel,planeAction_one]

def imaginaryUnit : K := algebraMap ℂ K Complex.I

theorem imaginaryUnit_sq : imaginaryUnit K ^ 2 = -1 := by
  rw [imaginaryUnit,← map_pow,Complex.I_sq,map_neg,map_one]

/-- Exact all-field four-plane transport in the actual symmetric-space/dual-space model. -/
theorem collision_reduced_fourPlane (g g' : Sp6 K) (U W : RhoFiber K)
    (h : planeAction K g U.val = planeAction K g' W.val) :
    ((rhoFiberEquiv K W).val).map (reducedDualEquiv K).toLinearMap =
      (((rhoFiberEquiv K U).val).map (reducedDualEquiv K).toLinearMap).map
        (dualSemidirectRepresentation K
          (M9.PrimitiveProjectiveStabilizer.toProjectiveSemidirect K (imaginaryUnit K)
            (imaginaryUnit_sq K) (collisionStabilizer K g g' U W h))) := by
  have hW : W.val.val = U.val.val.map
      (primitiveLinear K (collisionStabilizer K g g' U W h).val).toLinearMap := by
    have hh := congrArg (fun Z : RhoFiber K => Z.val.val) (collision_fiber_transport K g g' U W h).symm
    exact hh
  exact rhoFiberEquiv_dual_semidirect K (imaginaryUnit K) (imaginaryUnit_sq K)
    (collisionStabilizer K g g' U W h) U W hW

end M9Native.PrimitiveRadicalKernelPair
