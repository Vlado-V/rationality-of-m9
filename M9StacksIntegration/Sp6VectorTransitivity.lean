module

public import M9StacksIntegration.AlternatingTransvections
public import M9StacksIntegration.LagrangianTransitivity

/-!
# Genuine native Sp6 normalization of every nonzero six-vector

The actual native alternating form is nondegenerate in the original
e0,e1,e2,f0,f1,f2 coordinates. Genuine alternating transvections give
an actual preserving linear equivalence between any two nonzero vectors.
Its actual matrix, reindexed by the frozen splitIndex, satisfies literal
Mathlib J-preservation and therefore belongs to the original native
Matrix.symplecticGroup (Fin 3) K.

Both normalization directions are supplied. No arbitrary basis,
normalizer, nonzero pairing, transversality, infinite-field or
characteristic-zero premise is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Matrix

universe u

namespace M9Native.Sp6VectorTransitivity

open LagrangianRing LagrangianTransitivity

variable (K : Type u) [Field K]

theorem omega_e_right (v : Fin 6 → K) (j : Fin 3) :
    omega K v (e K j) = -v (fIndex j) := by
  fin_cases j <;>
    simp [omega_apply, omegaValue, e, basisVector, eIndex, fIndex, Fin.sum_univ_succ]

theorem omega_f_right (v : Fin 6 → K) (j : Fin 3) :
    omega K v (f K j) = v (eIndex j) := by
  fin_cases j <;>
    simp [omega_apply, omegaValue, f, basisVector, eIndex, fIndex, Fin.sum_univ_succ]

/-- Nondegeneracy of the original actual native six-coordinate form. -/
theorem omega_nondegenerate : (omega K).Nondegenerate := by
  have hleft : ∀ v : Fin 6 → K, (∀ w, omega K v w = 0) → v = 0 := by
    intro v hv
    funext i
    obtain ⟨j,rfl⟩ := splitIndex.surjective i
    cases j with
    | inl j =>
      change v (eIndex j) = 0
      have h := hv (f K j)
      rwa [omega_f_right] at h
    | inr j =>
      change v (fIndex j) = 0
      have h := hv (e K j)
      rw [omega_e_right, neg_eq_zero] at h
      exact h
  refine ⟨hleft, ?_⟩
  intro v hv
  apply hleft v
  intro w
  rw [omega_swap K v w, hv w, neg_zero]

/-- An actual form-preserving six-coordinate linear map gives a
literal element of the original native symplectic group. -/
def nativeSymplecticOfPreserving
    (f : (Fin 6 → K) →ₗ[K] (Fin 6 → K))
    (hf : ∀ v w, omega K (f v) (f w) = omega K v w) :
    Matrix.symplecticGroup (Fin 3) K := by
  have hB : ((standardForm K).toBilin').comp f f = (standardForm K).toBilin' := by
    refine LinearMap.ext (fun v => LinearMap.ext (fun w => ?_))
    change (standardForm K).toBilin' (f v) (f w) = (standardForm K).toBilin' v w
    rw [standardForm_bilin, standardForm_bilin, hf]
  have hM : (LinearMap.toMatrix' f)ᵀ * standardForm K * LinearMap.toMatrix' f =
      standardForm K := by
    have h := congrArg (fun B : LinearMap.BilinForm K (Fin 6 → K) => B.toMatrix') hB
    simpa only [LinearMap.BilinForm.toMatrix'_comp,
      LinearMap.BilinForm.toMatrix'_toBilin'] using h
  have hJ : (standardForm K).submatrix splitIndex splitIndex = Matrix.J (Fin 3) K := by
    ext i j
    simp only [standardForm, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  refine ⟨(LinearMap.toMatrix' f).submatrix splitIndex splitIndex,
    SymplecticGroup.mem_iff'.mpr ?_⟩
  calc
    ((LinearMap.toMatrix' f).submatrix splitIndex splitIndex)ᵀ * Matrix.J (Fin 3) K *
        (LinearMap.toMatrix' f).submatrix splitIndex splitIndex =
      ((LinearMap.toMatrix' f)ᵀ * standardForm K * LinearMap.toMatrix' f).submatrix
        splitIndex splitIndex := by
      rw [← hJ, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv,
        Matrix.submatrix_mul_equiv]
    _ = Matrix.J (Fin 3) K := by rw [hM, hJ]

theorem matrixSix_ofPreserving
    (f : (Fin 6 → K) →ₗ[K] (Fin 6 → K))
    (hf : ∀ v w, omega K (f v) (f w) = omega K v w) :
    matrixSix K (nativeSymplecticOfPreserving K f hf) = LinearMap.toMatrix' f := by
  ext i j
  change (LinearMap.toMatrix' f) (splitIndex (splitIndex.symm i))
    (splitIndex (splitIndex.symm j)) = _
  simp only [Equiv.apply_symm_apply]

theorem matrixSix_ofPreserving_mulVec
    (f : (Fin 6 → K) →ₗ[K] (Fin 6 → K))
    (hf : ∀ v w, omega K (f v) (f w) = omega K v w) (v : Fin 6 → K) :
    matrixSix K (nativeSymplecticOfPreserving K f hf) *ᵥ v = f v := by
  rw [matrixSix_ofPreserving, LinearMap.toMatrix'_mulVec]

/-- Literal native Sp6 acts transitively on the original nonzero
six-vectors over every field. -/
theorem exists_matrixSix_send (v w : Fin 6 → K) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : Matrix.symplecticGroup (Fin 3) K, matrixSix K g *ᵥ v = w := by
  obtain ⟨e, he, hpres⟩ := AlternatingTransvections.exists_preservingEquiv
    (omega K) (fun x => omega_self K x) (omega_nondegenerate K) v w hv hw
  exact ⟨nativeSymplecticOfPreserving K e.toLinearMap hpres,
    (matrixSix_ofPreserving_mulVec K e.toLinearMap hpres v).trans he⟩

theorem single_zero_ne_zero : (Pi.single (0 : Fin 6) (1 : K) : Fin 6 → K) ≠ 0 := by
  intro h
  exact (one_ne_zero : (1 : K) ≠ 0) (by simpa using congrFun h (0 : Fin 6))

/-- The consumer's direction: e0 maps to the given actual nonzero
vector, so annihilation of it becomes literal first-column zero. -/
theorem exists_matrixSix_send_e0 (v : Fin 6 → K) (hv : v ≠ 0) :
    ∃ g : Matrix.symplecticGroup (Fin 3) K,
      matrixSix K g *ᵥ Pi.single (0 : Fin 6) 1 = v :=
  exists_matrixSix_send K _ v (single_zero_ne_zero K) hv

/-- The reverse normalization, to the literal first basis vector. -/
theorem exists_matrixSix_send_to_e0 (v : Fin 6 → K) (hv : v ≠ 0) :
    ∃ g : Matrix.symplecticGroup (Fin 3) K,
      matrixSix K g *ᵥ v = Pi.single (0 : Fin 6) 1 :=
  exists_matrixSix_send K v _ hv (single_zero_ne_zero K)

end M9Native.Sp6VectorTransitivity
