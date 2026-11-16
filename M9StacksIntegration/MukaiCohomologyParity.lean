module

public import M9StacksIntegration.MukaiParityLinear
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections

/-!
# The native cohomology boundary in Mukai's parity argument

The boundary is chosen from the proved native right-derived global-sections
long exact sequence, restricted to the base field. Exactness is proved for
this specified map, without assuming an exact-sequence witness. The final bridge to an
alternating Serre cup product is treated separately in `MukaiParity`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] HasDerivedCategory.standard

namespace M9Native.MukaiCohomologyParity

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The connecting homomorphism supplied by the proved native long exact
sequence, read as a map of vector spaces over the base field. -/
def cohomologyBoundary {S : ShortComplex X.Modules} (hS : S.ShortExact) (n : ℕ) :
    cohomologyOverField k f S.X₃ n ⟶ cohomologyOverField k f S.X₁ (n+1) :=
  (exists_cohomologyOverField_longExactSequence k f hS).choose n

theorem cohomologyBoundary_injective_left {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    Function.Injective (cohomologyOverFieldMap k f S.f 0) :=
  (exists_cohomologyOverField_longExactSequence k f hS).choose_spec.1

theorem cohomologyBoundary_exact_left {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (cohomologyOverFieldMap k f S.f n)
      (cohomologyOverFieldMap k f S.g n) :=
  (exists_cohomologyOverField_longExactSequence k f hS).choose_spec.2.1 n

theorem cohomologyBoundary_exact_middle {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (cohomologyOverFieldMap k f S.g n) (cohomologyBoundary k f hS n) :=
  (exists_cohomologyOverField_longExactSequence k f hS).choose_spec.2.2.1 n

theorem cohomologyBoundary_exact_right {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (n : ℕ) :
    Function.Exact (cohomologyBoundary k f hS n)
      (cohomologyOverFieldMap k f S.f (n+1)) :=
  (exists_cohomologyOverField_longExactSequence k f hS).choose_spec.2.2.2 n

/-- The exact dimension identity for the specified native boundary. -/
theorem finrank_H0_add_boundary_range {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [Module.Finite k (cohomologyOverField k f S.X₂ 0)]
    [Module.Finite k (cohomologyOverField k f S.X₃ 0)] :
    Module.finrank k (cohomologyOverField k f S.X₂ 0) +
      Module.finrank k (LinearMap.range (cohomologyBoundary k f hS 0).hom) =
    Module.finrank k (cohomologyOverField k f S.X₁ 0) +
      Module.finrank k (cohomologyOverField k f S.X₃ 0) :=
  MukaiParityLinear.finrank_add_range_eq
    (cohomologyOverFieldMap k f S.f 0).hom (cohomologyOverFieldMap k f S.g 0).hom
    (cohomologyBoundary k f hS 0).hom
    (cohomologyBoundary_injective_left k f hS)
    (cohomologyBoundary_exact_left k f hS 0)
    (cohomologyBoundary_exact_middle k f hS 0)

/-- The native boundary and any explicitly constructed cup boundary have
the same rank if both fit the proved preceding cohomology map exactly. -/
theorem boundary_finrank_range_eq {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [Module.Finite k (cohomologyOverField k f S.X₂ 0)]
    [Module.Finite k (cohomologyOverField k f S.X₃ 0)]
    (δ : cohomologyOverField k f S.X₃ 0 →ₗ[k] cohomologyOverField k f S.X₁ 1)
    (hex : Function.Exact (cohomologyOverFieldMap k f S.g 0).hom δ) :
    Module.finrank k (LinearMap.range (cohomologyBoundary k f hS 0).hom) =
      Module.finrank k (LinearMap.range δ) :=
  MukaiParityLinear.finrank_range_eq_of_exact (cohomologyOverFieldMap k f S.g 0).hom
    (cohomologyBoundary k f hS 0).hom δ
    (cohomologyBoundary_exact_middle k f hS 0) hex

/-- A separately constructed cup boundary suffices: its exactness and
alternation give even rank for the native boundary, with no equality of
the two choices asserted. -/
theorem even_native_boundary_rank_of_exact_alternating [CharZero k]
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [Module.Finite k (cohomologyOverField k f S.X₂ 0)]
    [Module.Finite k (cohomologyOverField k f S.X₃ 0)]
    (δ : cohomologyOverField k f S.X₃ 0 →ₗ[k] cohomologyOverField k f S.X₁ 1)
    (hex : Function.Exact (cohomologyOverFieldMap k f S.g 0).hom δ)
    (p : cohomologyOverField k f S.X₃ 0 →ₗ[k]
      cohomologyOverField k f S.X₁ 1 →ₗ[k] k) (hp : p.IsPerfPair)
    (hAlt : ∀ x, p x (δ x) = 0) :
    Even (Module.finrank k (LinearMap.range (cohomologyBoundary k f hS 0).hom)) := by
  rw [boundary_finrank_range_eq k f hS δ hex]
  exact MukaiParityLinear.even_finrank_range_of_alternating_pairing p hp δ hAlt

/-- The specified native boundary yields parity after its actual Serre
pairing has been identified and its diagonal cup product shown to vanish.
These are explicit geometric gates, not an assumption that the result is even. -/
theorem even_H0_difference_of_boundary_alternating [CharZero k]
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [Module.Finite k (cohomologyOverField k f S.X₂ 0)]
    [Module.Finite k (cohomologyOverField k f S.X₃ 0)]
    (p : cohomologyOverField k f S.X₃ 0 →ₗ[k]
      cohomologyOverField k f S.X₁ 1 →ₗ[k] k) (hp : p.IsPerfPair)
    (hAlt : ∀ x, p x (cohomologyBoundary k f hS 0 x) = 0) :
    Even ((Module.finrank k (cohomologyOverField k f S.X₂ 0) : ℤ) -
      ((Module.finrank k (cohomologyOverField k f S.X₁ 0) : ℤ) -
        Module.finrank k (cohomologyOverField k f S.X₁ 1))) :=
  MukaiParityLinear.even_dimension_difference_of_exact_alternating
    (cohomologyOverFieldMap k f S.f 0).hom (cohomologyOverFieldMap k f S.g 0).hom
    (cohomologyBoundary k f hS 0).hom
    (cohomologyBoundary_injective_left k f hS)
    (cohomologyBoundary_exact_left k f hS 0)
    (cohomologyBoundary_exact_middle k f hS 0) p hp hAlt

/-- The linear algebra of Lemma 5.2 at the actual derived boundary: an
odd-dimensional injection into even-dimensional `H⁰` forces a nonzero
native first-cohomology class killed by the next boundary map. -/
theorem exists_nonzero_cohomology_boundary_kernel_of_odd_even
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [Subsingleton (cohomologyOverField k f S.X₁ 0)]
    [Module.Finite k (cohomologyOverField k f S.X₃ 0)]
    (hodd : Odd (Module.finrank k (cohomologyOverField k f S.X₂ 0)))
    (heven : Even (Module.finrank k (cohomologyOverField k f S.X₃ 0))) :
    ∃ ξ : cohomologyOverField k f S.X₁ 1,
      ξ ≠ 0 ∧ cohomologyOverFieldMap k f S.f 1 ξ = 0 :=
  by
    have hinj : Function.Injective (cohomologyOverFieldMap k f S.g 0).hom := by
      apply LinearMap.ker_eq_bot.mp
      rw [(cohomologyBoundary_exact_left k f hS 0).linearMap_ker_eq]
      apply LinearMap.range_eq_bot.mpr
      apply LinearMap.ext
      intro x
      rw [Subsingleton.elim x 0, map_zero]
      rfl
    exact MukaiParityLinear.exists_nonzero_kernel_of_odd_even_exact
      (cohomologyOverFieldMap k f S.g 0).hom (cohomologyBoundary k f hS 0).hom
      (cohomologyOverFieldMap k f S.f 1).hom hinj
      (cohomologyBoundary_exact_middle k f hS 0)
      (cohomologyBoundary_exact_right k f hS 0) hodd heven

end M9Native.MukaiCohomologyParity
