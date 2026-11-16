module

public import M9StacksIntegration.LagrangianTransitivity

/-! The explicit fixed symplectic identification between the quotient-row
and kernel-trivector conventions. All maps act on the actual exterior powers. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
open Matrix Module exteriorPower
universe u
namespace M9Native.LagrangianPluckerDuality
variable (R : Type u) [CommRing R]

/-- The fixed `J` identification, in the native first-three/last-three order. -/
def symplecticDuality : M9Native.LagrangianRing.V R →ₗ[R] M9Native.LagrangianRing.V R :=
  Matrix.toLin' (M9Native.LagrangianTransitivity.standardForm R)

theorem standardForm_squared :
    M9Native.LagrangianTransitivity.standardForm R *
      M9Native.LagrangianTransitivity.standardForm R = -1 := by
  unfold M9Native.LagrangianTransitivity.standardForm
  rw [Matrix.submatrix_mul_equiv,Matrix.J_squared]
  ext i j
  simp [Matrix.submatrix_apply,Matrix.one_apply]

/-- The fixed symplectic identification is an actual linear equivalence. -/
def symplecticDualityEquiv : M9Native.LagrangianRing.V R ≃ₗ[R] M9Native.LagrangianRing.V R := by
  refine LinearEquiv.ofLinearMap (Matrix.toLin' (M9Native.LagrangianTransitivity.standardForm R))
    (Matrix.toLin' (-M9Native.LagrangianTransitivity.standardForm R)) ?_ ?_
  · rw [← Matrix.toLin'_mul,Matrix.mul_neg,standardForm_squared,neg_neg,Matrix.toLin'_one]
  · rw [← Matrix.toLin'_mul,Matrix.neg_mul,standardForm_squared,neg_neg,Matrix.toLin'_one]

@[simp] theorem symplecticDualityEquiv_apply (v : M9Native.LagrangianRing.V R) :
    symplecticDualityEquiv R v=symplecticDuality R v := rfl

/-- The actual kernel partner of the `i`th quotient row. -/
def kernelPartner (M : Matrix (Fin 3) (Fin 6) R) (i : Fin 3) :
    M9Native.LagrangianRing.V R := symplecticDuality R (M i)

/-- The partner vector lies in the actual kernel whenever the actual rows are isotropic. -/
theorem kernelPartner_mem (M : Matrix (Fin 3) (Fin 6) R)
    (hM : ∀ i j,M9Native.LagrangianRing.omega R (M i) (M j)=0) (j : Fin 3) :
    kernelPartner R M j ∈ LinearMap.ker M.mulVecLin := by
  change M *ᵥ kernelPartner R M j=0
  ext i
  change (M i) ⬝ᵥ (M9Native.LagrangianTransitivity.standardForm R *ᵥ M j)=0
  rw [← Matrix.toBilin'_apply',M9Native.LagrangianTransitivity.standardForm_bilin,hM,neg_zero]

/-- The genuine kernel-valued frame obtained from the quotient rows by fixed `J`. -/
def kernelFrame (M : Matrix (Fin 3) (Fin 6) R)
    (hM : ∀ i j,M9Native.LagrangianRing.omega R (M i) (M j)=0) :
    Fin 3 → LinearMap.ker M.mulVecLin := fun i => ⟨kernelPartner R M i,kernelPartner_mem R M hM i⟩

/-- The explicit exterior transformation of the quotient-row trivector. -/
theorem rowPlucker_to_kernelPartner (M : Matrix (Fin 3) (Fin 6) R) :
    exteriorPower.map 3 (symplecticDuality R) (M9Native.LagrangianRing.rowPlucker R M)=
      exteriorPower.ιMulti R 3 (kernelPartner R M) := by
  rw [M9Native.LagrangianRing.rowPlucker,exteriorPower.map_apply_ιMulti]
  rfl

/-- The transported row trivector is literally the image of a trivector
in the actual quotient kernel, with the fixed `J` convention explicit. -/
theorem rowPlucker_to_kernel (M : Matrix (Fin 3) (Fin 6) R)
    (hM : ∀ i j,M9Native.LagrangianRing.omega R (M i) (M j)=0) :
    exteriorPower.map 3 (symplecticDuality R) (M9Native.LagrangianRing.rowPlucker R M)=
      exteriorPower.map 3 (LinearMap.ker M.mulVecLin).subtype
        (exteriorPower.ιMulti R 3 (kernelFrame R M hM)) := by
  rw [rowPlucker_to_kernelPartner,exteriorPower.map_apply_ιMulti]
  rfl

end M9Native.LagrangianPluckerDuality
