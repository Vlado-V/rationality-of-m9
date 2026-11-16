module

public import M9.RadicalMapProjective
public import M9.PrimitiveTwistedReduced
public import M9.PrimitiveEndomorphism

/-! # The actual primitive radical map and its distinguished fiber -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9.PrimitiveRadicalFiber

open Module ExteriorPrimitive PrimitiveStabilizer RadicalMap

variable (K : Type*) [Field K] [CharZero K]

local instance primitiveAddCommGroup : AddCommGroup (Primitive K) :=
  { (Primitive K).addCommGroup with toAddCommMonoid := (Primitive K).addCommMonoid }

/-- The actual odd-plane rank-eight locus, in the genuine primitive exterior kernel. -/
abbrev RankEightNinePlanes := RadicalMap.RankEightPlane (primitivePairing K)

/-- The actual projective radical-line map. -/
abbrev radicalLineMap : RankEightNinePlanes K → Projectivization K (Primitive K) :=
  RadicalMap.radicalPoint (primitivePairing K)

omit [CharZero K] in
/-- The wedge form is preserved by the genuine symplectic exterior action. -/
theorem primitivePairing_invariant (h : Sp6 K) (x y : Primitive K) :
    primitivePairing K (primitiveLinear K h x) (primitiveLinear K h y) =
      primitivePairing K x y := by
  change ambientPairing K (exteriorAction K h x.val) (exteriorAction K h y.val) =
    ambientPairing K x.val y.val
  have he := congrArg (ExteriorAlgebra.map h.val.toLinearMap)
    (mul_eq_pairing_smul_volume K x.val y.val)
  rw [map_mul,map_smul,PrimitiveEndomorphism.map_volume_of_det_one K h.val.toLinearMap
    (symplectic_det_one K h)] at he
  have hf := mul_eq_pairing_smul_volume K
    (exteriorAction K h x.val) (exteriorAction K h y.val)
  have hv : (volume K : ExteriorAlgebra K (V K)) ≠ 0 := by
    intro hz
    apply PrimitiveEndomorphism.orderedVolume_ne_zero K
    exact Subtype.coe_injective (by simpa using hz)
  apply smul_left_injective K hv
  apply hf.symm.trans
  simpa only [exteriorAction,exteriorPower.coe_map] using he

/-- The actual Sp6 action on the domain of the radical map. -/
def planeAction (h : Sp6 K) (U : RankEightNinePlanes K) : RankEightNinePlanes K :=
  RadicalMap.isometryPlane (primitivePairing K) (primitivePairing_isAlt K)
    (primitiveLinear K h) (primitivePairing_invariant K h) U

/-- Equivariance of the actual primitive radical-line map. -/
theorem radicalLineMap_equivariant (h : Sp6 K) (U : RankEightNinePlanes K) :
    radicalLineMap K (planeAction K h U) =
      Projectivization.map (primitiveLinear K h).toLinearMap (primitiveLinear K h).injective
        (radicalLineMap K U) :=
  RadicalMap.radicalPoint_isometry (primitivePairing K) (primitivePairing_isAlt K)
    (primitiveLinear K h) (primitivePairing_invariant K h) U

/-- The actual fiber over the line of a+b, without replacing it by a coordinate model. -/
abbrev RhoFiber := {U : RankEightNinePlanes K // radicalLineMap K U = rhoProjective K}

/-- Exact pointwise fiber comparison with nondegenerate four-planes in the actual
twelve-dimensional perpendicular-line quotient. -/
def rhoFiberEquiv : RhoFiber K ≃
    RadicalFiber.NondegenerateSubspace
      (RadicalFiber.reducedForm (primitivePairing K) (primitivePairing_isAlt K) (rhoLine K)) 4 :=
  (RadicalMap.pointFiberEquiv (primitivePairing K) (rhoProjective K)).trans
    (RadicalFiber.nineFourEquiv (primitivePairing K) (primitivePairing_isAlt K)
      (primitivePairing_nondegenerate K) (finrank_primitive K) (rhoLine K)
      (finrank_span_singleton (rho_ne_zero K)))

/-- The quotient in the fiber comparison has its actual dimension twelve. -/
theorem finrank_actualReduced : finrank K (PrimitiveBlockCoordinates.Reduced K) = 12 :=
  RadicalFiber.finrank_reduced_line (primitivePairing K) (primitivePairing_isAlt K)
    (primitivePairing_nondegenerate K) (finrank_primitive K) (rhoLine K)
    (finrank_span_singleton (rho_ne_zero K))

end M9.PrimitiveRadicalFiber
