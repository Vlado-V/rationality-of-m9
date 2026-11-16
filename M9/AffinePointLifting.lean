module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Lifting an actual affine rational point through a prime in its fiber

A prime above the kernel of a `K`-point can be enlarged to a maximal ideal.
For a finite-type algebra over an algebraically closed field, Zariski's
lemma and algebraic closedness turn that residue field into a `K`-point.
The point on the source is proved to restrict to the specified point.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9.AffinePointLifting

variable {K R S : Type*} [Field K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S]

/-- A point over its own coefficient field is automatically surjective. -/
theorem point_surjective (p : R →ₐ[K] K) : Function.Surjective p := by
  intro a
  exact ⟨algebraMap K R a, p.commutes a⟩

/-- The kernel of an actual `K`-point is an actual maximal ideal. -/
theorem point_kernel_isMaximal (p : R →ₐ[K] K) : (RingHom.ker p).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective p (point_surjective p)

/-- Enlarging the given prime does not change its contraction to the point kernel. -/
theorem exists_maximal_over_point (φ : R →ₐ[K] S) (p : R →ₐ[K] K)
    (q : Ideal S) [q.IsPrime]
    (hq : Ideal.comap φ.toRingHom q = RingHom.ker p) :
    ∃ m : Ideal S, m.IsMaximal ∧ q ≤ m ∧ Ideal.comap φ.toRingHom m = RingHom.ker p := by
  obtain ⟨m, hm, hqm⟩ := q.exists_le_maximal Ideal.IsPrime.ne_top'
  refine ⟨m, hm, hqm, ?_⟩
  apply Eq.symm
  apply (point_kernel_isMaximal p).eq_of_le (Ideal.comap_ne_top _ hm.ne_top)
  rw [← hq]
  exact Ideal.comap_mono hqm

/-- Equality on the coefficient field and the point kernel forces equality of the two points. -/
theorem comp_eq_of_kernel_le (φ : R →ₐ[K] S) (p : R →ₐ[K] K) (ψ : S →ₐ[K] K)
    (hker : RingHom.ker p ≤ Ideal.comap φ.toRingHom (RingHom.ker ψ)) :
    ψ.comp φ = p := by
  apply AlgHom.ext
  intro r
  have hr : r - algebraMap K R (p r) ∈ RingHom.ker p := by
    change p (r - algebraMap K R (p r)) = 0
    simp
  have hs := hker hr
  change ψ (φ (r - algebraMap K R (p r))) = 0 at hs
  have hs' : ψ (φ r) - p r = 0 := by
    simpa only [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] using hs
  exact sub_eq_zero.mp hs'

section AlgebraicallyClosed

variable [IsAlgClosed K] [Algebra.FiniteType K S]

/-- Weak Nullstellensatz for an arbitrary finite-type algebra, with the maximal ideal as kernel. -/
theorem exists_point_of_maximal (m : Ideal S) [m.IsMaximal] :
    ∃ ψ : S →ₐ[K] K, RingHom.ker ψ = m := by
  let : Field (S ⧸ m) := Ideal.Quotient.field m
  let : Module.Finite K (S ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (S ⧸ m)
  let : Algebra.IsAlgebraic K (S ⧸ m) := Algebra.IsAlgebraic.of_finite K (S ⧸ m)
  let χ : (S ⧸ m) →ₐ[K] K := IsAlgClosed.lift
  refine ⟨χ.comp (Ideal.Quotient.mkₐ K m), ?_⟩
  ext s
  change χ (Ideal.Quotient.mk m s) = 0 ↔ s ∈ m
  constructor
  · intro hs
    exact Ideal.Quotient.eq_zero_iff_mem.mp (χ.injective (by
      simpa only [map_zero, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hs))
  · intro hs
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hs, map_zero]

/-- The lifted rational point specializes the supplied prime and lies over the specified point. -/
theorem exists_point_lift_with_kernel (φ : R →ₐ[K] S) (p : R →ₐ[K] K)
    (q : Ideal S) [q.IsPrime]
    (hq : Ideal.comap φ.toRingHom q = RingHom.ker p) :
    ∃ ψ : S →ₐ[K] K, ψ.comp φ = p ∧ q ≤ RingHom.ker ψ := by
  obtain ⟨m, hm, hqm, hmp⟩ := exists_maximal_over_point φ p q hq
  let := hm
  obtain ⟨ψ, hψ⟩ := exists_point_of_maximal (K := K) m
  refine ⟨ψ, comp_eq_of_kernel_le φ p ψ ?_, ?_⟩
  · rw [hψ, hmp]
  · rw [hψ]
    exact hqm

/-- An actual rational point lifts through an actual prime in a finite-type fiber. -/
theorem exists_point_lift (φ : R →ₐ[K] S) (p : R →ₐ[K] K)
    (q : Ideal S) [q.IsPrime]
    (hq : Ideal.comap φ.toRingHom q = RingHom.ker p) :
    ∃ ψ : S →ₐ[K] K, ψ.comp φ = p := by
  obtain ⟨ψ, hψ, -⟩ := exists_point_lift_with_kernel φ p q hq
  exact ⟨ψ, hψ⟩

end AlgebraicallyClosed

end M9.AffinePointLifting
