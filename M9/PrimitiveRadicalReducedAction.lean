module

public import M9.PrimitiveRadicalSlice

/-! # The actual reduced-subspace action and the character twist

The character twist disappears on actual submodules. The action on the
actual quotient is therefore conjugate to the checked semidirect action
on the actual symmetric-matrix space and its true dual.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace M9.PrimitiveRadicalFiber

open Module ExteriorPrimitive PrimitiveStabilizer PrimitiveBlockCoordinates
open PrimitiveTwistedReduced

variable (K : Type*) [Field K] [CharZero K]

local instance primitiveReducedAddCommGroup : AddCommGroup (Primitive K) :=
  { (Primitive K).addCommGroup with toAddCommMonoid := (Primitive K).addCommMonoid }

local instance perpReducedAddCommGroup : AddCommGroup (Perp K) :=
  { (Perp K).addCommGroup with toAddCommMonoid := (Perp K).addCommMonoid }

/-- The actual inverse-character factor is nonzero. -/
theorem twistScalar_ne_zero (h : lineStabilizer K) : twistScalar K h ≠ 0 :=
  Units.ne_zero _

/-- Tensoring with the character line changes no actual subspace image. -/
theorem raw_twisted_submodule_map (i : K) (hi : i^2 = -1) (h : lineStabilizer K)
    (U : Submodule K (Reduced K)) :
    U.map (rawReducedAction K i hi h) = U.map (twistedReducedAction K i hi h) := by
  exact (Submodule.map_smul _ U (twistScalar K h) (twistScalar_ne_zero K h)).symm

/-- The raw quotient action on actual subspaces is the actual semidirect action
after the proved trace-duality coordinates. -/
theorem reducedDual_raw_submodule_map (i : K) (hi : i^2 = -1) (h : lineStabilizer K)
    (U : Submodule K (Reduced K)) :
    (U.map (rawReducedAction K i hi h)).map (reducedDualEquiv K).toLinearMap =
      (U.map (reducedDualEquiv K).toLinearMap).map
        (dualSemidirectRepresentation K
          (PrimitiveProjectiveStabilizer.toProjectiveSemidirect K i hi h)) := by
  rw [raw_twisted_submodule_map K i hi h U,← Submodule.map_comp,← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  exact reducedDualEquiv_twisted K i hi h

/-- Quotienting the actual ambient nine-plane commutes with the actual stabilizer action. -/
theorem quotientImage_natural (i : K) (hi : i^2 = -1) (h : lineStabilizer K)
    (U : Submodule K (Primitive K)) (hU : U ≤ Perp K) :
    RadicalFiber.quotientImage (primitivePairing K) (rhoLine K)
        (U.map (primitiveLinear K h.val).toLinearMap) =
      (RadicalFiber.quotientImage (primitivePairing K) (rhoLine K) U).map
        (rawReducedAction K i hi h) := by
  apply le_antisymm
  · rintro z ⟨x,hx,rfl⟩
    obtain ⟨y,hy,hxy⟩ := hx
    let yy : Perp K := ⟨y,hU hy⟩
    refine ⟨(Inside K).mkQ yy,⟨yy,hy,rfl⟩,?_⟩
    rw [rawReducedAction_mk]
    apply congrArg (Inside K).mkQ
    apply Subtype.ext
    exact hxy
  · rintro z ⟨q,hq,rfl⟩
    obtain ⟨x,hx,rfl⟩ := hq
    refine ⟨rawPerpAction K i hi h x,⟨x.val,hx,rfl⟩,rfl⟩

/-- The raw quotient action is an actual linear isomorphism. -/
def rawReducedLinear (i : K) (hi : i^2 = -1) (h : lineStabilizer K) : Reduced K ≃ₗ[K] Reduced K :=
  LinearEquiv.ofLinearMap (rawReducedAction K i hi h) (rawReducedAction K i hi h⁻¹)
    (by rw [← rawReducedAction_mul,mul_inv_cancel,rawReducedAction_one])
    (by rw [← rawReducedAction_mul,inv_mul_cancel,rawReducedAction_one])

/-- It preserves the genuine quotient bilinear form. -/
theorem rawReducedLinear_isometry (i : K) (hi : i^2 = -1) (h : lineStabilizer K) :
    ∀ x y : Reduced K,
      RadicalFiber.reducedForm (primitivePairing K) (primitivePairing_isAlt K) (rhoLine K)
          (rawReducedLinear K i hi h x) (rawReducedLinear K i hi h y) =
        RadicalFiber.reducedForm (primitivePairing K) (primitivePairing_isAlt K) (rhoLine K) x y := by
  intro x y
  refine Submodule.Quotient.induction_on (Inside K) x ?_
  intro x
  refine Submodule.Quotient.induction_on (Inside K) y ?_
  intro y
  change RadicalFiber.reducedForm _ _ _
      ((Inside K).mkQ (rawPerpAction K i hi h x)) ((Inside K).mkQ (rawPerpAction K i hi h y)) =
    RadicalFiber.reducedForm _ _ _ ((Inside K).mkQ x) ((Inside K).mkQ y)
  rw [RadicalFiber.reducedForm_mk,RadicalFiber.reducedForm_mk]
  exact primitivePairing_invariant K h.val x.val y.val

omit [CharZero K] in
private theorem orthogonal_isometry_map {W : Type*} [AddCommGroup W] [Module K W]
    (B : LinearMap.BilinForm K W) (g : W ≃ₗ[K] W)
    (hg : ∀ x y, B (g x) (g y) = B x y) (U : Submodule K W) :
    B.orthogonal (U.map g.toLinearMap) = (B.orthogonal U).map g.toLinearMap := by
  apply le_antisymm
  · intro y hy
    refine ⟨g.symm y,?_,g.apply_symm_apply y⟩
    intro x hx
    have he := hg x (g.symm y)
    rw [g.apply_symm_apply] at he
    exact he.symm.trans (hy (g x) ⟨x,hx,rfl⟩)
  · rintro y ⟨x,hx,rfl⟩
    rintro z ⟨w,hw,rfl⟩
    exact (hg w x).trans (hx w hw)

/-- The actual four-plane fiber comparison respects actual stabilizer transport.
The hypothesis merely records which actual ambient plane is the transported plane. -/
theorem rhoFiberEquiv_natural (i : K) (hi : i^2 = -1) (h : lineStabilizer K)
    (U W : RhoFiber K)
    (hW : W.val.val = U.val.val.map (primitiveLinear K h.val).toLinearMap) :
    (rhoFiberEquiv K W).val =
      ((rhoFiberEquiv K U).val).map (rawReducedAction K i hi h) := by
  have hu : RadicalFiber.radical (primitivePairing K) U.val.val = rhoLine K :=
    ((RadicalMap.pointFiberEquiv (primitivePairing K) (rhoProjective K)) U).property.2
  have hup : U.val.val ≤ Perp K :=
    RadicalFiber.radical_le_perp (primitivePairing K) (primitivePairing_isAlt K) _ _ hu
  change (RadicalFiber.reducedForm (primitivePairing K) (primitivePairing_isAlt K) (rhoLine K)).orthogonal
      (RadicalFiber.quotientImage (primitivePairing K) (rhoLine K) W.val.val) =
    ((RadicalFiber.reducedForm (primitivePairing K) (primitivePairing_isAlt K) (rhoLine K)).orthogonal
      (RadicalFiber.quotientImage (primitivePairing K) (rhoLine K) U.val.val)).map _
  rw [hW,quotientImage_natural K i hi h U.val.val hup]
  exact orthogonal_isometry_map K _ (rawReducedLinear K i hi h)
    (rawReducedLinear_isometry K i hi h) _

/-- Complete fiber/action comparison in the actual `Symmetric3 ⊕ Dual Symmetric3` model. -/
theorem rhoFiberEquiv_dual_semidirect (i : K) (hi : i^2 = -1) (h : lineStabilizer K)
    (U W : RhoFiber K)
    (hW : W.val.val = U.val.val.map (primitiveLinear K h.val).toLinearMap) :
    ((rhoFiberEquiv K W).val).map (reducedDualEquiv K).toLinearMap =
      (((rhoFiberEquiv K U).val).map (reducedDualEquiv K).toLinearMap).map
        (dualSemidirectRepresentation K
          (PrimitiveProjectiveStabilizer.toProjectiveSemidirect K i hi h)) := by
  rw [rhoFiberEquiv_natural K i hi h U W hW,reducedDual_raw_submodule_map]

/-- The literal stabilizer action on actual points of the distinguished radical fiber. -/
def stabilizerFiberMap (h : lineStabilizer K) (U : RhoFiber K) : RhoFiber K := by
  refine ⟨planeAction K h.val U.val,?_⟩
  rw [radicalLineMap_equivariant]
  change projectiveAction K h.val (radicalLineMap K U.val) = rhoProjective K
  rw [U.property]
  exact h.property

/-- Concrete equivariance of the actual fiber comparison, with its actual stabilizer action. -/
theorem rhoFiberEquiv_dual_semidirect_action (i : K) (hi : i^2 = -1) (h : lineStabilizer K)
    (U : RhoFiber K) :
    ((rhoFiberEquiv K (stabilizerFiberMap K h U)).val).map (reducedDualEquiv K).toLinearMap =
      (((rhoFiberEquiv K U).val).map (reducedDualEquiv K).toLinearMap).map
        (dualSemidirectRepresentation K
          (PrimitiveProjectiveStabilizer.toProjectiveSemidirect K i hi h)) :=
  rhoFiberEquiv_dual_semidirect K i hi h U (stabilizerFiberMap K h U) rfl

end M9.PrimitiveRadicalFiber
