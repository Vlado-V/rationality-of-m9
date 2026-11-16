module

public import M9StacksIntegration.LagrangianTransitivity

/-! A polynomial symplectic shear for an arbitrary original plane.
The correction term handles a nonisotropic plane without division. All
identities are over an arbitrary commutative ring, for later use on
actual projective-line chart rings. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Matrix Module

universe u

namespace M9Native.SymplecticPlaneShear

open LagrangianRing LagrangianTransitivity
variable (R : Type u) [CommRing R]

/-- The corrected rank-two nilpotent, in the actual native form. -/
def operator (w0 w1 c : V R) : V R →ₗ[R] V R :=
  (omega R c).smulRight w1 + (omega R w1).smulRight c -
    omega R w0 w1 • (omega R c).smulRight c

theorem operator_apply (w0 w1 c v : V R) :
    operator R w0 w1 c v = omega R c v • w1 + omega R w1 v • c -
      (omega R w0 w1 * omega R c v) • c := by
  simp only [operator,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    LinearMap.smulRight_apply,smul_smul]

theorem operator_c (w0 w1 c : V R) (h1c : omega R w1 c = 0) :
    operator R w0 w1 c c = 0 := by
  rw [operator_apply]
  simp only [omega_self,h1c,zero_smul,mul_zero,zero_add,sub_zero]

theorem operator_second (w0 w1 c : V R) (h1c : omega R w1 c = 0) :
    operator R w0 w1 c w1 = 0 := by
  have hc1 : omega R c w1 = 0 := by rw [omega_swap R c w1,h1c,neg_zero]
  rw [operator_apply]
  simp only [hc1,omega_self,zero_smul,mul_zero,zero_add,sub_zero]

/-- The correction exactly cancels the original plane's pairing. -/
theorem operator_first (w0 w1 c : V R) (h0c : omega R w0 c = 1) :
    operator R w0 w1 c w0 = -w1 := by
  have hc0 : omega R c w0 = -1 := by rw [omega_swap R c w0,h0c]
  rw [operator_apply,hc0,omega_swap R w1 w0]
  simp only [mul_neg_one,neg_smul,one_smul]
  abel

theorem operator_square (w0 w1 c v : V R) (h1c : omega R w1 c = 0) :
    operator R w0 w1 c (operator R w0 w1 c v) = 0 := by
  rw [operator_apply R w0 w1 c v]
  simp only [map_add,map_sub,map_smul,operator_second R w0 w1 c h1c,
    operator_c R w0 w1 c h1c,smul_zero,add_zero,sub_zero]

/-- The actual infinitesimal symplectic identity is computed from the
literal alternating form, not assumed. -/
theorem operator_lie (w0 w1 c v z : V R) :
    omega R (operator R w0 w1 c v) z + omega R v (operator R w0 w1 c z) = 0 := by
  rw [operator_apply R w0 w1 c v,operator_apply R w0 w1 c z]
  simp only [map_add,map_sub,map_smul,LinearMap.add_apply,LinearMap.sub_apply,
    LinearMap.smul_apply,smul_eq_mul]
  rw [omega_swap R v w1,omega_swap R v c]
  ring

theorem operator_image_isotropic (w0 w1 c v z : V R) (h1c : omega R w1 c = 0) :
    omega R (operator R w0 w1 c v) (operator R w0 w1 c z) = 0 := by
  have hc1 : omega R c w1 = 0 := by rw [omega_swap R c w1,h1c,neg_zero]
  rw [operator_apply R w0 w1 c v,operator_apply R w0 w1 c z]
  simp only [map_add,map_sub,map_smul,LinearMap.add_apply,LinearMap.sub_apply,
    LinearMap.smul_apply,smul_eq_mul,omega_self,h1c,hc1,mul_zero,
    add_zero,sub_self]

def shearMap (w0 w1 c : V R) (t : R) : V R →ₗ[R] V R :=
  LinearMap.id - t • operator R w0 w1 c

theorem shearMap_apply (w0 w1 c v : V R) (t : R) :
    shearMap R w0 w1 c t v = v - t • operator R w0 w1 c v := rfl

/-- This is the genuine all-ring preservation equation for the original
six-coordinate form. -/
theorem shearMap_preserves (w0 w1 c : V R) (h1c : omega R w1 c = 0) (t : R)
    (v z : V R) :
    omega R (shearMap R w0 w1 c t v) (shearMap R w0 w1 c t z) = omega R v z := by
  rw [shearMap_apply,shearMap_apply]
  simp only [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul]
  rw [operator_image_isotropic R w0 w1 c v z h1c]
  have h := operator_lie R w0 w1 c v z
  linear_combination -t * h

theorem shearMap_neg_comp (w0 w1 c : V R) (h1c : omega R w1 c = 0) (t : R) :
    (shearMap R w0 w1 c (-t)).comp (shearMap R w0 w1 c t) = LinearMap.id := by
  apply LinearMap.ext
  intro v
  change (v - t • operator R w0 w1 c v) -
    (-t) • operator R w0 w1 c (v - t • operator R w0 w1 c v) = v
  rw [map_sub,map_smul,operator_square R w0 w1 c v h1c]
  simp only [smul_zero,sub_zero,neg_smul,sub_neg_eq_add]
  abel

/-- The native J-matrix membership test follows from actual form
preservation over a commutative ring. No field is needed here. -/
def ringSymplecticOfPreserving (f : V R →ₗ[R] V R)
    (hf : ∀ v z,omega R (f v) (f z) = omega R v z) :
    Matrix.symplecticGroup (Fin 3) R := by
  have hB : ((standardForm R).toBilin').comp f f = (standardForm R).toBilin' := by
    refine LinearMap.ext (fun v => LinearMap.ext (fun z => ?_))
    change (standardForm R).toBilin' (f v) (f z) = (standardForm R).toBilin' v z
    rw [standardForm_bilin,standardForm_bilin,hf]
  have hM : (LinearMap.toMatrix' f)ᵀ * standardForm R * LinearMap.toMatrix' f = standardForm R := by
    have h := congrArg (fun B : LinearMap.BilinForm R (V R) => B.toMatrix') hB
    simpa only [LinearMap.BilinForm.toMatrix'_comp,LinearMap.BilinForm.toMatrix'_toBilin'] using h
  have hJ : (standardForm R).submatrix splitIndex splitIndex = Matrix.J (Fin 3) R := by
    ext i j
    simp only [standardForm,Matrix.submatrix_apply,Equiv.symm_apply_apply]
  refine ⟨(LinearMap.toMatrix' f).submatrix splitIndex splitIndex,
    SymplecticGroup.mem_iff'.mpr ?_⟩
  calc
    _ = ((LinearMap.toMatrix' f)ᵀ * standardForm R * LinearMap.toMatrix' f).submatrix
        splitIndex splitIndex := by
      rw [← hJ,Matrix.transpose_submatrix,Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
    _ = Matrix.J (Fin 3) R := by rw [hM,hJ]

theorem matrixSix_ofRingPreserving (f : V R →ₗ[R] V R)
    (hf : ∀ v z,omega R (f v) (f z) = omega R v z) :
    matrixSix R (ringSymplecticOfPreserving R f hf) = LinearMap.toMatrix' f := by
  ext i j
  change (LinearMap.toMatrix' f) (splitIndex (splitIndex.symm i))
    (splitIndex (splitIndex.symm j)) = _
  simp only [Equiv.apply_symm_apply]

/-- The actual native symplectic matrix is constructed from the proved
polynomial shear, not supplied as a normal-form witness. -/
def shear (w0 w1 c : V R) (h1c : omega R w1 c = 0) (t : R) :
    Matrix.symplecticGroup (Fin 3) R :=
  ringSymplecticOfPreserving R (shearMap R w0 w1 c t) (shearMap_preserves R w0 w1 c h1c t)

theorem matrixSix_shear_mulVec (w0 w1 c v : V R) (h1c : omega R w1 c = 0) (t : R) :
    matrixSix R (shear R w0 w1 c h1c t) *ᵥ v = shearMap R w0 w1 c t v := by
  rw [shear,matrixSix_ofRingPreserving,LinearMap.toMatrix'_mulVec]

/-- The actual polynomial matrix sends the original first plane vector
to the actual line parameter, for every value in every coefficient ring. -/
theorem shear_sends_first (w0 w1 c : V R) (h0c : omega R w0 c = 1)
    (h1c : omega R w1 c = 0) (t : R) :
    matrixSix R (shear R w0 w1 c h1c t) *ᵥ w0 = w0 + t • w1 := by
  rw [matrixSix_shear_mulVec,shearMap_apply,operator_first R w0 w1 c h0c]
  simp only [smul_neg,sub_neg_eq_add]

end M9Native.SymplecticPlaneShear
