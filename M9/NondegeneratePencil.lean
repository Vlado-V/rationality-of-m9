module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# A nonsingular matrix subspace has dimension at most one

Over an algebraically closed field, a pencil through an invertible square
matrix contains a singular member: apply the eigenvalue theorem to A⁻¹B.
Consequently a linear subspace whose every nonzero matrix is nonsingular
has dimension at most one.

This is the linear-algebra step used in Mukai's Section 6 after proving that
every nonzero bivector in the kernel of exterior evaluation is nondegenerate.
The theorem below does not assume the existence or classification of a Mukai
bundle. It applies to arbitrary square matrices, including the empty-index
case in the dimension theorem.
-/

@[expose] public noncomputable section

namespace M9.NondegeneratePencil

open Matrix Module

variable {K ι : Type*} [Field K] [IsAlgClosed K] [Fintype ι] [DecidableEq ι]

/-- An actual nonzero kernel vector appears in some member of the pencil
through an invertible matrix. -/
theorem exists_pencil_kernel [Nonempty ι] (A B : Matrix ι ι K)
    (hA : A.det ≠ 0) :
    ∃ (c : K) (v : ι → K), v ≠ 0 ∧ (B - c • A) *ᵥ v = 0 := by
  classical
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' (A⁻¹ * B))
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have heig : (A⁻¹ * B) *ᵥ v = c • v := hv.apply_eq_smul
  have heq := congrArg (fun w : ι → K => A *ᵥ w) heig
  have hB : B *ᵥ v = c • (A *ᵥ v) := by
    simpa only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_left A B hu,
      Matrix.mulVec_smul] using heq
  refine ⟨c, v, hv.2, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hB, sub_self]

/-- Every pencil through an invertible square matrix has an actual singular
member over an algebraically closed field. -/
theorem exists_pencil_det_zero [Nonempty ι] (A B : Matrix ι ι K)
    (hA : A.det ≠ 0) : ∃ c : K, (B - c • A).det = 0 := by
  obtain ⟨c, v, hv, hcv⟩ := exists_pencil_kernel A B hA
  refine ⟨c, ?_⟩
  by_contra hdet
  have hu : IsUnit (B - c • A) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hu
  apply hv
  apply hinj
  simpa only [Matrix.mulVec_zero] using hcv

/-- Two members of a subspace consisting of nonsingular nonzero matrices are
proportional, once the first member is nonzero. -/
theorem exists_smul_eq [Nonempty ι] (S : Submodule K (Matrix ι ι K))
    (hS : ∀ M ∈ S, M ≠ 0 → M.det ≠ 0)
    {A B : Matrix ι ι K} (hAS : A ∈ S) (hBS : B ∈ S) (hA : A ≠ 0) :
    ∃ c : K, c • A = B := by
  obtain ⟨c, hc⟩ := exists_pencil_det_zero A B (hS A hAS hA)
  have hzero : B - c • A = 0 := by
    by_contra hne
    exact hS _ (S.sub_mem hBS (S.smul_mem c hAS)) hne hc
  exact ⟨c, (sub_eq_zero.mp hzero).symm⟩

/-- A subspace all of whose nonzero square matrices are nonsingular has
dimension at most one. No positive size hypothesis is needed. -/
theorem finrank_le_one (S : Submodule K (Matrix ι ι K))
    (hS : ∀ M ∈ S, M ≠ 0 → M.det ≠ 0) : Module.finrank K S ≤ 1 := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · let := hι
    rw [Module.finrank_zero_of_subsingleton]
    exact Nat.zero_le _
  · let := hι
    by_cases hbot : S = ⊥
    · subst S
      exact le_trans (le_of_eq (_root_.finrank_bot K (Matrix ι ι K))) (Nat.zero_le _)
    · obtain ⟨A, hAS, hA⟩ := S.ne_bot_iff.mp hbot
      apply _root_.finrank_le_one (⟨A, hAS⟩ : S)
      intro B
      obtain ⟨c, hc⟩ := exists_smul_eq S hS hAS B.property hA
      exact ⟨c, Subtype.ext hc⟩

/-- The dimension result transfers to any actual vector space having an
injective matrix realization that sends nonzero vectors to nonsingular
matrices. This includes a kernel of alternating evaluation after choosing
its genuine matrix coordinates. -/
theorem finrank_le_one_of_injective_matrix_model
    {V : Type*} [AddCommGroup V] [Module K V]
    (f : V →ₗ[K] Matrix ι ι K) (hf : Function.Injective f)
    (hdet : ∀ v : V, v ≠ 0 → (f v).det ≠ 0) : Module.finrank K V ≤ 1 := by
  rw [← LinearMap.finrank_range_of_inj hf]
  apply finrank_le_one f.range
  rintro M ⟨v, rfl⟩ hv
  exact hdet v (fun hz => hv (by rw [hz, map_zero]))

/-- A nonzero nonsingular matrix subspace is exactly a line. -/
theorem finrank_eq_one (S : Submodule K (Matrix ι ι K))
    (hS : ∀ M ∈ S, M ≠ 0 → M.det ≠ 0) (hne : S ≠ ⊥) :
    Module.finrank K S = 1 := by
  let : Nontrivial S := S.nontrivial_iff_ne_bot.mpr hne
  exact Nat.le_antisymm (finrank_le_one S hS)
    (Nat.succ_le_of_lt (Module.finrank_pos (R := K) (M := S)))

/-- The precise rank-nullity consequence used for Mukai's exterior-square
evaluation: when the domain has one more dimension than the target and
the actual kernel has a faithful nonsingular matrix realization, its kernel
is a line and the original evaluation map is surjective. -/
theorem kernel_line_and_surjective
    {V W : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (hdim : Module.finrank K V = Module.finrank K W + 1)
    (j : f.ker →ₗ[K] Matrix ι ι K) (hj : Function.Injective j)
    (hdet : ∀ v : f.ker, v ≠ 0 → (j v).det ≠ 0) :
    Module.finrank K f.ker = 1 ∧ Function.Surjective f := by
  have hk := finrank_le_one_of_injective_matrix_model j hj hdet
  have hr := f.finrank_range_add_finrank_ker
  have hrle : Module.finrank K f.range ≤ Module.finrank K W := Submodule.finrank_le _
  have hkone : Module.finrank K f.ker = 1 := by omega
  refine ⟨hkone, LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq ?_)⟩
  omega

end M9.NondegeneratePencil
