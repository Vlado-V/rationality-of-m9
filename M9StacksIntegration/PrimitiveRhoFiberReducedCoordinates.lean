module

public import M9StacksIntegration.PrimitiveRadicalKernelPair
public import M9StacksIntegration.PrimitiveMixedScalarExtension

/-! Actual reduced four-plane coordinates of the literal rho-fiber quotient kernels. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module
open scoped Classical Matrix

namespace M9Native.PrimitiveRhoFiberReducedCoordinates
open M9.ExteriorPrimitive M9.PrimitiveStabilizer M9.PrimitiveBlockCoordinates M9.PrimitiveRadicalFiber
open PrimitiveRhoFiberChart PrimitiveRhoFiberFieldPoints PrimitiveRhoFiberNondegenerate

variable (K : Type) [Field K] [Algebra ℂ K]
local instance extensionCharZero : CharZero K := PrimitiveExtensionFieldBridge.charZero_extension K
local instance primitiveGroup : AddCommGroup (Primitive K) :=
  { (Primitive K).addCommGroup with toAddCommMonoid := (Primitive K).addCommMonoid }
local instance perpGroup : AddCommGroup (Perp K) :=
  { (Perp K).addCommGroup with toAddCommMonoid := (Perp K).addCommMonoid }

abbrev reducedPairing : LinearMap.BilinForm K (Reduced K) :=
  M9.RadicalFiber.reducedForm (primitivePairing K) (primitivePairing_isAlt K) (rhoLine K)

def reducedCoordinates : Reduced K ≃ₗ[K] (Fin 12 → K) :=
  (reducedDualEquiv K).trans (ReducedGraphAction.actualCoordinates K)

def mixedPerpFrame (P : Matrix (Fin 12) (Fin 4) K) : (Fin 4 → K) →ₗ[K] Perp K :=
  (mixedFrame K P).codRestrict (Perp K) (by
    intro x l hl
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hl
    have hx := rho_orthogonal_mixedPlane K P (mixedFrame K P x) ⟨x,rfl⟩
    have hρ : primitivePairing K (rho K) (mixedFrame K P x) = 0 := by
      rw [primitivePairing_neg_swap,hx,neg_zero]
    simp only [map_smul,LinearMap.smul_apply,hρ,smul_zero])

def reducedFrame (P : Matrix (Fin 12) (Fin 4) K) : (Fin 4 → K) →ₗ[K] Reduced K :=
  (Inside K).mkQ.comp (mixedPerpFrame K P)

theorem reducedFrame_coordinates (P : Matrix (Fin 12) (Fin 4) K) (x : Fin 4 → K) :
    reducedCoordinates K (reducedFrame K P x) = P *ᵥ x := by
  have hRL : retractionMatrix.map (algebraMap ℂ K) * liftMatrix.map (algebraMap ℂ K) = 1 := by
    rw [← Matrix.map_mul,retractionMatrix_liftMatrix,Matrix.map_one] <;> simp
  change ReducedGraphAction.actualCoordinates K
    (M9.PrimitiveTwistedReduced.mixedDualEquiv K
      (reducedEquiv K ((Inside K).mkQ (mixedPerpFrame K P x)))) = _
  rw [reducedEquiv_mk]
  change ReducedGraphAction.actualCoordinates K
    (M9.PrimitiveTwistedReduced.mixedDualEquiv K (mixedProjection K (mixedFrame K P x))) = _
  rw [PrimitiveMixedScalarExtension.actualCoordinates_mixedProjection,mixedFrame_coordinates,
    Matrix.mulVec_mulVec,← Matrix.mul_assoc,hRL,Matrix.one_mul]

theorem reducedFrame_nondegenerate (P : Matrix (Fin 12) (Fin 4) K)
    (hP : (gramMatrix K P).det ≠ 0) :
    ((reducedPairing K).compl₁₂ (reducedFrame K P) (reducedFrame K P)).Nondegenerate := by
  have hB : (reducedPairing K).compl₁₂ (reducedFrame K P) (reducedFrame K P) =
      (primitivePairing K).compl₁₂ (mixedFrame K P) (mixedFrame K P) := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact M9.RadicalFiber.reducedForm_mk (primitivePairing K) (primitivePairing_isAlt K)
      (rhoLine K) (mixedPerpFrame K P x) (mixedPerpFrame K P y)
  rw [hB]
  exact mixedFrame_pullback_nondegenerate K P hP

def reducedPlane (P : Matrix (Fin 12) (Fin 4) K) : Submodule K (Reduced K) :=
  (reducedFrame K P).range

theorem reducedPlane_finrank (P : Matrix (Fin 12) (Fin 4) K) (hP : (gramMatrix K P).det ≠ 0) :
    finrank K (reducedPlane K P) = 4 := by
  let e := LinearEquiv.ofInjective (reducedFrame K P)
    (injective_of_pullback_nondegenerate K _ _ (reducedFrame_nondegenerate K P hP))
  simpa [reducedPlane] using e.finrank_eq.symm

def nondegeneratePlane (P : Matrix (Fin 12) (Fin 4) K) (hP : (gramMatrix K P).det ≠ 0) :
    M9.RadicalFiber.NondegenerateSubspace (reducedPairing K) 4 :=
  ⟨reducedPlane K P,reducedPlane_finrank K P hP,
    restrict_range_nondegenerate K _ _ (reducedFrame_nondegenerate K P hP)⟩

/-- The actual quotient coordinates of the lifted frame retain every original P entry. -/
theorem reducedCoordinates_plane (P : Matrix (Fin 12) (Fin 4) K) :
    (reducedPlane K P).map (reducedCoordinates K).toLinearMap = (Matrix.toLin' P).range := by
  rw [reducedPlane,← LinearMap.range_comp]
  congr 1
  apply LinearMap.ext
  exact reducedFrame_coordinates K P

/-- The actual quotient and perpendicular construction recovers the original
literal nine-plane kernel, before making any coordinate identification. -/
theorem orthogonal_reducedPlane_preimage (P : Matrix (Fin 12) (Fin 4) K) :
    M9.RadicalFiber.quotientPreimage (primitivePairing K) (rhoLine K)
      ((reducedPairing K).orthogonal (reducedPlane K P)) = quotientKernel K P := by
  rw [quotientKernel_eq_orthogonalPlane]
  ext x
  constructor
  · rintro ⟨v,hv,rfl⟩
    change (Inside K).mkQ v ∈ (reducedPairing K).orthogonal (reducedPlane K P) at hv
    intro w hw
    obtain ⟨r,hr,m,hm,rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨t,rfl⟩ := hm
    have hm : primitivePairing K (mixedFrame K P t) v.val = 0 := by
      exact hv (reducedFrame K P t) ⟨t,rfl⟩
    change primitivePairing K (r + mixedFrame K P t) v.val = 0
    rw [map_add,LinearMap.add_apply,v.property r hr,hm,zero_add]
  · intro hx
    have hρ : x ∈ Perp K := by
      intro r hr
      exact hx r ((le_sup_left : rhoLine K ≤ rhoLine K ⊔ mixedPlane K P) hr)
    refine ⟨⟨x,hρ⟩,?_,rfl⟩
    intro z hz
    obtain ⟨t,rfl⟩ := hz
    change primitivePairing K (mixedFrame K P t) x = 0
    exact hx (mixedFrame K P t)
      ((le_sup_right : mixedPlane K P ≤ rhoLine K ⊔ mixedPlane K P) ⟨t,rfl⟩)

/-- The genuine intrinsic fiber equivalence selects exactly the lifted reduced
four-plane. This identifies the specific equivalence, rather than just dimensions. -/
theorem rhoFiberEquiv_rhoFiberPoint (P : Matrix (Fin 12) (Fin 4) K)
    (hP : (gramMatrix K P).det ≠ 0) :
    rhoFiberEquiv K (PrimitiveRadicalKernelPair.rhoFiberPoint K P hP) =
      nondegeneratePlane K P hP := by
  apply (rhoFiberEquiv K).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Subtype.ext
  apply Subtype.ext
  change quotientKernel K P =
    M9.RadicalFiber.quotientPreimage (primitivePairing K) (rhoLine K)
      ((reducedPairing K).orthogonal (reducedPlane K P))
  exact (orthogonal_reducedPlane_preimage K P).symm

/-- Literal original graph columns are the coordinates of the actual fiber point. -/
theorem rhoFiberEquiv_coordinates (P : Matrix (Fin 12) (Fin 4) K)
    (hP : (gramMatrix K P).det ≠ 0) :
    ((rhoFiberEquiv K (PrimitiveRadicalKernelPair.rhoFiberPoint K P hP)).val).map
      (reducedCoordinates K).toLinearMap = (Matrix.toLin' P).range := by
  rw [rhoFiberEquiv_rhoFiberPoint]
  exact reducedCoordinates_plane K P

/-- The nondegenerate localization discharges the Gram condition at every
actual field point, with the original graph coefficients unchanged. -/
theorem rhoFiberEquiv_fieldPoint_coordinates (f : nondegenerateRing →ₐ[ℂ] K) :
    ((rhoFiberEquiv K (PrimitiveRadicalKernelPair.fieldPoint K f)).val).map
      (reducedCoordinates K).toLinearMap =
        (Matrix.toLin' (localizedGraph.map f)).range :=
  rhoFiberEquiv_coordinates K _ (fieldPoint_gram_det_ne_zero f)

end M9Native.PrimitiveRhoFiberReducedCoordinates
