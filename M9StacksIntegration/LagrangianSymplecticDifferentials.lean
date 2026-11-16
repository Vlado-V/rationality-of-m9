module

public import M9StacksIntegration.LagrangianCotangentFormula
public import M9StacksIntegration.LagrangianTransitivity

/-! The intrinsic differential formula is invariant under actual constant symplectic matrices. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Module Matrix
open scoped BigOperators

universe u v w

namespace M9Native.LagrangianSymplecticDifferentials

open LagrangianCotangentFormula LagrangianTransitivity

variable {k : Type u} {R : Type v} [CommRing k] [CommRing R] [Algebra k R]
  {M : Type w} [AddCommGroup M] [Module R M] [Module k M]
  {Q : Type*} [AddCommGroup Q] [Module R Q]

/-- Matrix multiplication with a genuine module-valued column. -/
def moduleMulVec (G : Matrix (Fin 6) (Fin 6) R) (y : Fin 6 → M) : Fin 6 → M :=
  fun i => ∑ j,G i j • y j

/-- A scalar matrix paired with a scalar and a module-valued column. -/
def moduleBilinear (P : Matrix (Fin 6) (Fin 6) R) (x : Fin 6 → R) (y : Fin 6 → M) : M :=
  ∑ i,∑ j,(x i * P i j) • y j

/-- The ordinary matrix congruence identity remains valid with a
module-valued second vector. -/
theorem moduleBilinear_congruence (P G : Matrix (Fin 6) (Fin 6) R)
    (x : Fin 6 → R) (y : Fin 6 → M) :
    moduleBilinear P (G*ᵥx) (moduleMulVec G y)=
      moduleBilinear (Gᵀ*P*G) x y := by
  simp only [moduleBilinear,moduleMulVec,Matrix.mulVec,dotProduct,
    Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul,Finset.mul_sum,
    Finset.sum_smul,Finset.smul_sum,smul_smul]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    intro a
    arg 2
    intro b
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    intro i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  conv_lhs =>
    arg 2
    intro i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  ring

/-- The literal six-coordinate symplectic pairing with a module-valued
second vector, in the original `e,f` order. -/
def mixedPair (x : Fin 6 → R) (y : Fin 6 → M) : M :=
  ∑ i : Fin 3,(x (i.castAdd 3) • y (Fin.natAdd 3 i)-
    x (Fin.natAdd 3 i) • y (i.castAdd 3))

theorem mixedPair_eq_matrix (x : Fin 6 → R) (y : Fin 6 → M) :
    mixedPair x y=moduleBilinear (-standardForm R) x y := by
  simp [mixedPair,moduleBilinear,standardForm,Matrix.J,Matrix.fromBlocks,
    Matrix.one_apply,splitIndex,finSumFinEquiv,Fin.sum_univ_succ]
  norm_num [Fin.addCases]
  all_goals module

/-- The genuine symplectic matrix equation gives preservation of the
module-valued pairing; no chosen module basis is required. -/
theorem mixedPair_preserved (G : Matrix (Fin 6) (Fin 6) R)
    (hG : Gᵀ * standardForm R * G=standardForm R)
    (x : Fin 6 → R) (y : Fin 6 → M) :
    mixedPair (G*ᵥx) (moduleMulVec G y)=mixedPair x y := by
  rw [mixedPair_eq_matrix,mixedPair_eq_matrix,moduleBilinear_congruence,
    Matrix.mul_neg,Matrix.neg_mul,hG]

/-- Differentiating a constant matrix times a column is the same
module-valued matrix times the column of derivatives. -/
theorem derivation_mulVec (d : Derivation k R M) (G : Matrix (Fin 6) (Fin 6) R)
    (hG : ∀ i j,d (G i j)=0) (x : Fin 6 → R) :
    (fun i => d ((G*ᵥx) i))=moduleMulVec G (fun i => d (x i)) := by
  funext i
  simp only [Matrix.mulVec,dotProduct,moduleMulVec,map_sum,Derivation.leibniz,
    hG,smul_zero,zero_add,add_zero]

/-- The intrinsic actual differential formula is invariant under a
constant matrix satisfying the genuine symplectic matrix equation. -/
theorem differentialPair_constant_symplectic (d : Derivation k R M)
    (G : Matrix (Fin 6) (Fin 6) R)
    (hG : Gᵀ * standardForm R * G=standardForm R)
    (hconst : ∀ i j,d (G i j)=0)
    (c : Q →ₗ[R] (Fin 6 → R)) (α β : Q) :
    differentialPair d (G.mulVecLin.comp c) α β=differentialPair d c α β := by
  change mixedPair (G*ᵥ(c α)) (fun i => d ((G*ᵥ(c β)) i))=
    mixedPair (c α) (fun i => d (c β i))
  rw [derivation_mulVec d G hconst]
  exact mixedPair_preserved G hG _ _

end M9Native.LagrangianSymplecticDifferentials
