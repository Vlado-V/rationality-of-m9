module

public import M9StacksIntegration.PrimitiveRhoFiberFieldPoints

/-! Transport of the intrinsic primitive radical to the fixed fourteen coordinates. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Matrix Module

namespace M9Native.PrimitiveCoordinateRadical

section Transport
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem radical_map_equiv (B : LinearMap.BilinForm K V) (C : LinearMap.BilinForm K W)
    (hB : B.IsRefl) (hC : C.IsRefl) (e : V ≃ₗ[K] W)
    (he : ∀ x y, C (e x) (e y) = B x y) (U : Submodule K V) :
    (M9.RadicalFiber.radical B U).map e.toLinearMap =
      M9.RadicalFiber.radical C (U.map e.toLinearMap) := by
  apply le_antisymm
  · rintro y ⟨x,hx,rfl⟩
    obtain ⟨hxU,hxB⟩ := (M9.RadicalFiber.mem_radical_iff B hB U x).mp hx
    apply (M9.RadicalFiber.mem_radical_iff C hC _ _).mpr
    refine ⟨⟨x,hxU,rfl⟩,?_⟩
    rintro z ⟨w,hw,rfl⟩
    exact (he x w).trans (hxB w hw)
  · intro y hy
    obtain ⟨hyU,hyC⟩ := (M9.RadicalFiber.mem_radical_iff C hC _ y).mp hy
    obtain ⟨x,hx,rfl⟩ := hyU
    refine ⟨x,?_,rfl⟩
    apply (M9.RadicalFiber.mem_radical_iff B hB U x).mpr
    refine ⟨hx,?_⟩
    intro w hw
    exact (he x w).symm.trans (hyC (e w) ⟨w,hw,rfl⟩)

end Transport

open M9.ExteriorPrimitive M9.PrimitiveStabilizer
open PrimitiveExtensionFieldBridge PrimitiveRhoFiberFieldPoints

variable (K : Type) [Field K] [Algebra ℂ K]
local instance extensionCharZero : CharZero K := charZero_extension K
local instance primitiveGroup : AddCommGroup (Primitive K) :=
  { (Primitive K).addCommGroup with toAddCommMonoid := (Primitive K).addCommMonoid }

def coordinateForm : LinearMap.BilinForm K (Fin 14 → K) :=
  (PrimitiveRhoFiberChart.pairingMatrix.map (algebraMap ℂ K)).toBilin'

theorem coordinateForm_isAlt : (coordinateForm K).IsAlt := by
  intro x
  obtain ⟨w,rfl⟩ := (fieldCoordinates K).surjective x
  change (PrimitiveRhoFiberChart.pairingMatrix.map (algebraMap ℂ K)).toBilin'
    (fieldCoordinates K w) (fieldCoordinates K w) = 0
  rw [← coordinates_pairing K]
  exact primitivePairing_isAlt K w

theorem coordinate_radical_span (N : Matrix (Fin 5) (Fin 14) K) (w : Primitive K)
    (hRad : M9.RadicalFiber.radical (primitivePairing K)
      ((LinearMap.ker N.mulVecLin).map (fieldCoordinates K).symm.toLinearMap) =
        Submodule.span K {w}) :
    M9.RadicalFiber.radical (coordinateForm K) (LinearMap.ker N.mulVecLin) =
      Submodule.span K {fieldCoordinates K w} := by
  let U := (LinearMap.ker N.mulVecLin).map (fieldCoordinates K).symm.toLinearMap
  have hU : U.map (fieldCoordinates K).toLinearMap = LinearMap.ker N.mulVecLin := by
    apply le_antisymm
    · rintro y ⟨x,⟨v,hv,rfl⟩,rfl⟩
      change N *ᵥ fieldCoordinates K ((fieldCoordinates K).symm v) = 0
      rw [LinearEquiv.apply_symm_apply]
      exact hv
    · intro v hv
      exact ⟨(fieldCoordinates K).symm v,⟨v,hv,rfl⟩,(fieldCoordinates K).apply_symm_apply v⟩
  have h := radical_map_equiv (primitivePairing K) (coordinateForm K)
    (primitivePairing_isAlt K).isRefl (coordinateForm_isAlt K).isRefl
    (fieldCoordinates K) (fun x y => (coordinates_pairing K x y).symm) U
  rw [hU,hRad] at h
  rw [← h,Submodule.map_span,Set.image_singleton]
  rfl

end M9Native.PrimitiveCoordinateRadical
