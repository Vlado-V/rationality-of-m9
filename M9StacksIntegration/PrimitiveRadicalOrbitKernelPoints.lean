module

public import M9StacksIntegration.PrimitiveRadicalOrbitPoints

/-! Exact original primitive kernels and intrinsic radicals of native orbit-family field points. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module AlgebraicGeometry CategoryTheory
open scoped Classical Matrix

namespace M9Native.PrimitiveRadicalOrbitKernelPoints
open M9.ExteriorPrimitive M9.PrimitiveStabilizer M9.PrimitiveRadicalFiber
open PrimitiveExtensionFieldBridge PrimitiveRadicalOrbitPoints
open M9.PrimitiveBlockCoordinates M9.PrimitiveTwistedReduced

variable (K : Type) [Field K] [Algebra ℂ K]
local instance extensionCharZero : CharZero K := charZero_extension K
local instance primitiveGroup : AddCommGroup (Primitive K) :=
  { (Primitive K).addCommGroup with toAddCommMonoid := (Primitive K).addCommMonoid }
local instance perpGroup : AddCommGroup (Perp K) :=
  { (Perp K).addCommGroup with toAddCommMonoid := (Perp K).addCommMonoid }

/-- The actual original symplectic group point of the literal evaluated Gauss matrix. -/
def originalGroupAt (y : Point K) : Sp6 K := toOriginal K (gaussAt K y)

/-- Literal kernel of the acted native quotient, in the original exterior module over K. -/
def kernelAt (y : Point K) : Submodule K (Primitive K) :=
  (Matrix.toLin' (quotientAt K y)).ker.map (fieldCoordinates K).symm.toLinearMap

def planeAt (y : Point K) : RankEightNinePlanes K :=
  planeAction K (originalGroupAt K y) (PrimitiveRadicalKernelPair.fieldPoint K (rightPoint K y)).val

omit [Algebra ℂ K] in
theorem primitiveLinear_inv (g : Sp6 K) : primitiveLinear K g⁻¹ = (primitiveLinear K g).symm := by
  change (primitiveRepresentation K) g⁻¹ = ((primitiveRepresentation K) g)⁻¹
  exact map_inv _ _

theorem primitiveInverseAt_coordinates (y : Point K) (v : Primitive K) :
    primitiveInverseAt K y *ᵥ fieldCoordinates K v =
      fieldCoordinates K ((primitiveLinear K (originalGroupAt K y)).symm v) := by
  have h := primitiveMatrix_fieldCoordinates K ((gaussAt K y)⁻¹) v
  rw [map_inv,primitiveLinear_inv] at h
  exact h

/-- Inverse precomposition of the original quotient is precisely original primitive transport. -/
theorem kernelAt_eq_map (y : Point K) : kernelAt K y =
    (PrimitiveRhoFiberFieldPoints.quotientKernel K (graphAt K y)).map
      (primitiveLinear K (originalGroupAt K y)).toLinearMap := by
  ext v
  rw [kernelAt,Submodule.mem_map_equiv]
  simp only [LinearEquiv.symm_symm,LinearMap.mem_ker,Matrix.toLin'_apply]
  rw [Submodule.mem_map_equiv,PrimitiveRhoFiberFieldPoints.quotientKernel,Submodule.mem_map_equiv]
  simp only [LinearEquiv.symm_symm,LinearMap.mem_ker,Matrix.toLin'_apply]
  rw [quotientAt,← Matrix.mulVec_mulVec,primitiveInverseAt_coordinates]

theorem kernelAt_eq_planeAt (y : Point K) : kernelAt K y = (planeAt K y).val :=
  kernelAt_eq_map K y

theorem kernelAt_finrank (y : Point K) : finrank K (kernelAt K y) = 9 := by
  rw [kernelAt_eq_planeAt]
  exact (planeAt K y).property.1

/-- The original acted kernel has exactly the actual Gauss transform of the original rho line. -/
theorem kernelAt_radical (y : Point K) :
    M9.RadicalFiber.radical (primitivePairing K) (kernelAt K y) =
      K ∙ (primitiveLinear K (originalGroupAt K y) (rho K)) := by
  rw [kernelAt_eq_map,← M9.RadicalMap.radical_map_isometry
    (primitivePairing K) (primitivePairing_isAlt K) (primitiveLinear K (originalGroupAt K y))
      (primitivePairing_invariant K (originalGroupAt K y))]
  have hρ := (PrimitiveRhoFiberFieldPoints.fieldPoint_kernel_finrank_radical K (rightPoint K y)).2
  change M9.RadicalFiber.radical (primitivePairing K)
      (PrimitiveRhoFiberFieldPoints.quotientKernel K (graphAt K y)) = rhoLine K at hρ
  rw [hρ,rhoLine,Submodule.map_span,Set.image_singleton]
  rfl

/-- Native scheme-point equality is exactly equality of the original transported primitive planes. -/
theorem nativePoint_eq_iff_planeAt_eq (y z : Point K) :
    nativePoint K y = nativePoint K z ↔ planeAt K y = planeAt K z := by
  have hbase : nativePoint K y ≫ GrassmannianCharts.projection ℂ 9 14 =
      nativePoint K z ≫ GrassmannianCharts.projection ℂ 9 14 := by
    rw [nativePoint_projection,nativePoint_projection]
  rw [GrassmannianFieldKernels.points_eq_iff_kernel_eq (K := K) (k := 9) (n := 14)
    (nativePoint K y) (nativePoint K z) (quotientAt K y) (quotientAt K z)
    (quotientAt_surjective K y) (quotientAt_surjective K z)
    (nativePoint_class K y) (nativePoint_class K z) hbase]
  constructor
  · intro h
    apply Subtype.ext
    rw [← kernelAt_eq_planeAt,← kernelAt_eq_planeAt]
    exact congrArg (fun U => U.map (fieldCoordinates K).symm.toLinearMap) h
  · intro h
    apply Submodule.map_injective_of_injective
      (f := (fieldCoordinates K).symm.toLinearMap) (fieldCoordinates K).symm.injective
    change kernelAt K y = kernelAt K z
    rw [kernelAt_eq_planeAt,kernelAt_eq_planeAt,h]

/-- Equality of actual native family images produces an actual stabilizer element. -/
def collisionStabilizerAt (y z : Point K) (h : nativePoint K y = nativePoint K z) : lineStabilizer K :=
  PrimitiveRadicalKernelPair.collisionStabilizer K (originalGroupAt K y) (originalGroupAt K z)
    (PrimitiveRadicalKernelPair.fieldPoint K (rightPoint K y))
    (PrimitiveRadicalKernelPair.fieldPoint K (rightPoint K z)) ((nativePoint_eq_iff_planeAt_eq K y z).mp h)

theorem collisionStabilizerAt_val (y z : Point K) (h : nativePoint K y = nativePoint K z) :
    (collisionStabilizerAt K y z h).val = (originalGroupAt K z)⁻¹ * originalGroupAt K y := rfl

theorem collisionStabilizerAt_transport (y z : Point K) (h : nativePoint K y = nativePoint K z) :
    stabilizerFiberMap K (collisionStabilizerAt K y z h)
      (PrimitiveRadicalKernelPair.fieldPoint K (rightPoint K y)) =
        PrimitiveRadicalKernelPair.fieldPoint K (rightPoint K z) :=
  PrimitiveRadicalKernelPair.collision_fiber_transport K (originalGroupAt K y) (originalGroupAt K z)
    (PrimitiveRadicalKernelPair.fieldPoint K (rightPoint K y))
    (PrimitiveRadicalKernelPair.fieldPoint K (rightPoint K z)) ((nativePoint_eq_iff_planeAt_eq K y z).mp h)

/-- Native orbit-family collisions have exactly the actual reduced-four-plane semidirect transport. -/
theorem collision_reduced_fourPlane (y z : Point K) (h : nativePoint K y = nativePoint K z) :
    ((rhoFiberEquiv K (PrimitiveRadicalKernelPair.fieldPoint K (rightPoint K z))).val).map
        (reducedDualEquiv K).toLinearMap =
      (((rhoFiberEquiv K (PrimitiveRadicalKernelPair.fieldPoint K (rightPoint K y))).val).map
        (reducedDualEquiv K).toLinearMap).map
          (dualSemidirectRepresentation K
            (M9.PrimitiveProjectiveStabilizer.toProjectiveSemidirect K
              (PrimitiveRadicalKernelPair.imaginaryUnit K) (PrimitiveRadicalKernelPair.imaginaryUnit_sq K)
              (collisionStabilizerAt K y z h))) :=
  PrimitiveRadicalKernelPair.collision_reduced_fourPlane K (originalGroupAt K y) (originalGroupAt K z)
    (PrimitiveRadicalKernelPair.fieldPoint K (rightPoint K y))
    (PrimitiveRadicalKernelPair.fieldPoint K (rightPoint K z)) ((nativePoint_eq_iff_planeAt_eq K y z).mp h)

end M9Native.PrimitiveRadicalOrbitKernelPoints
