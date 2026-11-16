module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Tactic

/-!
# Finite-dimensional algebra in Mukai's parity argument

An alternating connecting map, interpreted through a perfect pairing, has
even rank. The exact sequence `0 → A → B → C → D` then computes the parity
of `dim B`. No geometric parity hypothesis occurs in these lemmas.

This is the elementary linear algebra used by Proposition 1.2 and Lemma 5.2
of S. Mukai, *Curves and symmetric spaces, II*, Ann. Math. 172 (2010).
-/

@[expose] public noncomputable section

namespace M9Native.MukaiParityLinear

open Module LinearMap

variable {k : Type*} [Field k] [CharZero k]

/-- A nondegenerate alternating form has even dimension. The proof is the
determinant identity of its actual skew-symmetric matrix. -/
theorem even_finrank_of_nondegenerate_alternating
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate) (hAlt : B.IsAlt) :
    Even (finrank k V) := by
  let b := Module.finBasis k V
  let M := LinearMap.BilinForm.toMatrix b B
  have hdet : M.det ≠ 0 := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB
  have hskew : M.transpose = -M := by
    ext i j
    change (LinearMap.BilinForm.toMatrix b B) j i =
      -(LinearMap.BilinForm.toMatrix b B) i j
    simp only [LinearMap.BilinForm.toMatrix_apply]
    exact (hAlt.neg_eq (b i) (b j)).symm
  have hd := congrArg Matrix.det hskew
  rw [Matrix.det_transpose, Matrix.det_neg, Fintype.card_fin] at hd
  have hp : (-1 : k) ^ finrank k V = 1 :=
    mul_right_cancel₀ hdet (by simpa only [one_mul] using hd.symm)
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : k) ≠ 1)).mp hp

omit [CharZero k] in
/-- Restricting an alternating form to a complement of its actual kernel
gives a nondegenerate form. -/
theorem nondegenerate_restrict_kernel_complement
    {V : Type*} [AddCommGroup V] [Module k V]
    (B : LinearMap.BilinForm k V) (hAlt : B.IsAlt)
    (W : Submodule k V) (hW : IsCompl W (LinearMap.ker B)) :
    (B.restrict W).Nondegenerate := by
  have hleft : (B.restrict W).SeparatingLeft := by
    intro x hx
    have hxker : x.val ∈ LinearMap.ker B := by
      rw [LinearMap.mem_ker]
      apply LinearMap.ext
      intro y
      change B x.val y = 0
      obtain ⟨w, z, hw, hz, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hW.codisjoint y
      rw [map_add]
      have hzw : B z x.val = 0 := LinearMap.congr_fun (LinearMap.mem_ker.mp hz) x.val
      have hxz : B x.val z = 0 := by rw [← hAlt.neg_eq, hzw, neg_zero]
      rw [show B x.val w = 0 from hx ⟨w,hw⟩, hxz, add_zero]
    have hmem : x.val ∈ W ⊓ LinearMap.ker B := ⟨x.property,hxker⟩
    rw [hW.inf_eq_bot] at hmem
    apply Subtype.ext
    change x.val = 0
    simpa only [Submodule.mem_bot] using hmem
  refine ⟨hleft, ?_⟩
  intro x hx
  apply hleft x
  intro y
  change B x.val y.val = 0
  rw [← hAlt.neg_eq, show B y.val x.val = 0 from hx y, neg_zero]

/-- The rank of any alternating bilinear form is even, including when it
has a radical. -/
theorem even_finrank_range_alternating
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (B : LinearMap.BilinForm k V) (hAlt : B.IsAlt) :
    Even (finrank k (LinearMap.range B)) := by
  obtain ⟨W,hW⟩ := Submodule.exists_isCompl (LinearMap.ker B)
  have heven := even_finrank_of_nondegenerate_alternating (B.restrict W)
    (nondegenerate_restrict_kernel_complement B hAlt W hW.symm)
    (fun x => hAlt x.val)
  have hdim := Submodule.finrank_add_eq_of_isCompl hW
  have hrank := B.finrank_range_add_finrank_ker
  have heq : finrank k (LinearMap.range B) = finrank k W := by omega
  rw [heq]
  exact heven

/-- An actual connecting linear map has even rank when its diagonal cup
pairing vanishes and the comparison pairing is perfect. -/
theorem even_finrank_range_of_alternating_pairing
    {C D : Type*} [AddCommGroup C] [Module k C] [FiniteDimensional k C]
    [AddCommGroup D] [Module k D]
    (p : C →ₗ[k] D →ₗ[k] k) (hp : p.IsPerfPair) (δ : C →ₗ[k] D)
    (hAlt : ∀ x, p x (δ x) = 0) : Even (finrank k (LinearMap.range δ)) := by
  let B : LinearMap.BilinForm k C := p.flip.comp δ
  have hB : B.IsAlt := hAlt
  have hker : LinearMap.ker B = LinearMap.ker δ := by
    ext x
    simp only [LinearMap.mem_ker]
    change p.flip (δ x) = 0 ↔ δ x = 0
    exact hp.bijective_right.injective.eq_iff' (map_zero p.flip)
  have hrankB := B.finrank_range_add_finrank_ker
  have hrankδ := δ.finrank_range_add_finrank_ker
  rw [hker] at hrankB
  have heq : finrank k (LinearMap.range δ) = finrank k (LinearMap.range B) := by omega
  rw [heq]
  exact even_finrank_range_alternating B hB

section ExactSequence

variable {A B C D : Type*}
  [AddCommGroup A] [Module k A] [FiniteDimensional k A]
  [AddCommGroup B] [Module k B] [FiniteDimensional k B]
  [AddCommGroup C] [Module k C] [FiniteDimensional k C]
  [AddCommGroup D] [Module k D] [FiniteDimensional k D]

omit [CharZero k] [FiniteDimensional k A] [FiniteDimensional k D] in
/-- The dimension equation of an actual four-term exact sequence. -/
theorem finrank_add_range_eq (a : A →ₗ[k] B) (b : B →ₗ[k] C) (δ : C →ₗ[k] D)
    (ha : Function.Injective a) (hab : Function.Exact a b) (hbδ : Function.Exact b δ) :
    finrank k B + finrank k (LinearMap.range δ) = finrank k A + finrank k C := by
  have hb := b.finrank_range_add_finrank_ker
  have hδ := δ.finrank_range_add_finrank_ker
  rw [hab.linearMap_ker_eq, LinearMap.finrank_range_of_inj ha] at hb
  rw [hbδ.linearMap_ker_eq] at hδ
  omega

omit [CharZero k] [FiniteDimensional k A] [FiniteDimensional k B]
  [FiniteDimensional k D] in
/-- The rank of a connecting map is independent of the choice of the
map once the preceding map and exactness are fixed. This permits comparison
with a cup-product boundary through its kernel, without identifying choices. -/
theorem finrank_range_eq_of_exact (b : B →ₗ[k] C) (δ δ' : C →ₗ[k] D)
    (hδ : Function.Exact b δ) (hδ' : Function.Exact b δ') :
    finrank k (LinearMap.range δ) = finrank k (LinearMap.range δ') := by
  have hd := δ.finrank_range_add_finrank_ker
  have hd' := δ'.finrank_range_add_finrank_ker
  rw [hδ.linearMap_ker_eq] at hd
  rw [hδ'.linearMap_ker_eq] at hd'
  omega

omit [FiniteDimensional k A] [FiniteDimensional k D] in
/-- The parity conclusion is derived from exactness and the actual
alternating connecting map, not supplied as an assumption. -/
theorem even_dimension_difference_of_exact_alternating
    (a : A →ₗ[k] B) (b : B →ₗ[k] C) (δ : C →ₗ[k] D)
    (ha : Function.Injective a) (hab : Function.Exact a b) (hbδ : Function.Exact b δ)
    (p : C →ₗ[k] D →ₗ[k] k) (hp : p.IsPerfPair)
    (hAlt : ∀ x, p x (δ x) = 0) :
    Even ((finrank k B : ℤ) - ((finrank k A : ℤ) - finrank k D)) := by
  have hdim := finrank_add_range_eq a b δ ha hab hbδ
  let := hp
  have hCD : finrank k C = finrank k D := Module.finrank_of_isPerfPair p
  rw [hCD] at hdim
  obtain ⟨n,hn⟩ := even_finrank_range_of_alternating_pairing p hp δ hAlt
  refine ⟨(finrank k D : ℤ) - n, ?_⟩
  omega

omit [CharZero k] [FiniteDimensional k A] [FiniteDimensional k C]
  [FiniteDimensional k D] in
/-- The odd-to-even dimension obstruction in Mukai's Lemma 5.2 produces
an actual nonzero vector in the next kernel. -/
theorem exists_nonzero_kernel_of_odd_even_exact
    (a : A →ₗ[k] B) (b : B →ₗ[k] C) (δ : C →ₗ[k] D)
    (ha : Function.Injective a) (hab : Function.Exact a b) (hbδ : Function.Exact b δ)
    (hA : Odd (finrank k A)) (hB : Even (finrank k B)) :
    ∃ x : C, x ≠ 0 ∧ δ x = 0 := by
  by_contra h
  push Not at h
  have hbzero : b = 0 := by
    ext x
    by_contra hne
    exact h (b x) hne (congrFun hbδ.comp_eq_zero x)
  have hdim := b.finrank_range_add_finrank_ker
  rw [hab.linearMap_ker_eq, LinearMap.finrank_range_of_inj ha,
    hbzero, LinearMap.range_zero, finrank_bot] at hdim
  obtain ⟨m,hm⟩ := hA
  obtain ⟨n,hn⟩ := hB
  omega

end ExactSequence

end M9Native.MukaiParityLinear
