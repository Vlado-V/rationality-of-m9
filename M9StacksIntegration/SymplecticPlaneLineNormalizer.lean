module

public import M9StacksIntegration.SymplecticPlanePartner
public import M9StacksIntegration.SymplecticPlaneShear

/-! Genuine coefficient-ring normalizers of the line in an arbitrary
original independent plane. The native symplectic matrix is constructed
uniformly from the proved partner and polynomial shear, without a
symplectic-plane or field-valued-parameter premise. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open Matrix Module
universe u

namespace M9Native.SymplecticPlaneLineNormalizer

open LagrangianRing LagrangianTransitivity SymplecticPlanePartner SymplecticPlaneShear

variable (K : Type u) [Field K]

/-- The original vector with its actual coefficients mapped to a ring. -/
def constantVector {R : Type u} [CommRing R] (ρ : K →+* R) (v : V K) : V R := ρ ∘ v

theorem omega_constantVector {R : Type u} [CommRing R] (ρ : K →+* R) (v z : V K) :
    omega R (constantVector K ρ v) (constantVector K ρ z) = ρ (omega K v z) := by
  simp [omega_apply,omegaValue,constantVector,map_sum,map_sub,map_mul]

/-- A genuine constant native symplectic matrix, from actual vector
transitivity, sends the original first basis vector to w0. -/
def firstMatrix (w : Fin 2 → V K) (hw : LinearIndependent K w) :
    Matrix.symplecticGroup (Fin 3) K :=
  Classical.choose (Sp6VectorTransitivity.exists_matrixSix_send_e0 K (w 0) (hw.ne_zero 0))

theorem firstMatrix_sends_first (w : Fin 2 → V K) (hw : LinearIndependent K w) :
    matrixSix K (firstMatrix K w hw) *ᵥ Pi.single (0 : Fin 6) 1 = w 0 :=
  Classical.choose_spec (Sp6VectorTransitivity.exists_matrixSix_send_e0 K (w 0) (hw.ne_zero 0))

omit [Field K] in
theorem matrixSix_mul {R : Type u} [CommRing R]
    (g h : Matrix.symplecticGroup (Fin 3) R) :
    matrixSix R (g*h) = matrixSix R g * matrixSix R h := by
  change ((g : Matrix SplitIndex SplitIndex R)*(h : Matrix SplitIndex SplitIndex R)).submatrix
    splitIndex.symm splitIndex.symm = _
  exact (Matrix.submatrix_mul_equiv _ _ splitIndex.symm splitIndex.symm splitIndex.symm).symm

omit [Field K] in
theorem matrixSix_one {R : Type u} [CommRing R] :
    matrixSix R (1 : Matrix.symplecticGroup (Fin 3) R) = 1 := by
  change (1 : Matrix SplitIndex SplitIndex R).submatrix splitIndex.symm splitIndex.symm = 1
  exact Matrix.submatrix_one_equiv splitIndex.symm

/-- The actual native matrix exists over every coefficient ring,
including the genuine projective-line chart rings. -/
def normalizer (w : Fin 2 → V K) (hw : LinearIndependent K w)
    {R : Type u} [CommRing R] (ρ : K →+* R) (t : R) :
    Matrix.symplecticGroup (Fin 3) R :=
  shear R (constantVector K ρ (w 0)) (constantVector K ρ (w 1))
    (constantVector K ρ (commonPartner K w hw))
    (by rw [omega_constantVector,omega_second_commonPartner,map_zero]) t *
      mapSymplectic K ρ (firstMatrix K w hw)

theorem normalizer_sends_first (w : Fin 2 → V K) (hw : LinearIndependent K w)
    {R : Type u} [CommRing R] (ρ : K →+* R) (t : R) :
    matrixSix R (normalizer K w hw ρ t) *ᵥ Pi.single (0 : Fin 6) 1 =
      constantVector K ρ (w 0) + t • constantVector K ρ (w 1) := by
  have hbase : matrixSix R (mapSymplectic K ρ (firstMatrix K w hw)) *ᵥ
      Pi.single (0 : Fin 6) 1 = constantVector K ρ (w 0) := by
    rw [matrixSix_map,Matrix.mulVec_single_one]
    funext i
    change ρ (matrixSix K (firstMatrix K w hw) i 0) = ρ (w 0 i)
    apply congrArg ρ
    have h := congrFun (firstMatrix_sends_first K w hw) i
    simpa only [Matrix.mulVec_single_one,Matrix.col_apply] using h
  rw [normalizer,matrixSix_mul,← Matrix.mulVec_mulVec,hbase]
  apply shear_sends_first
  rw [omega_constantVector,omega_first_commonPartner,map_one]

theorem normalizer_inverse_sends_line (w : Fin 2 → V K) (hw : LinearIndependent K w)
    {R : Type u} [CommRing R] (ρ : K →+* R) (t : R) :
    matrixSix R (normalizer K w hw ρ t)⁻¹ *ᵥ
      (constantVector K ρ (w 0) + t • constantVector K ρ (w 1)) =
        Pi.single (0 : Fin 6) 1 := by
  rw [← normalizer_sends_first K w hw ρ t,Matrix.mulVec_mulVec,
    ← matrixSix_mul,inv_mul_cancel,matrixSix_one,Matrix.one_mulVec]

end M9Native.SymplecticPlaneLineNormalizer
