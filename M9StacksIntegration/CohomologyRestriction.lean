module

public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic

/-!
# Restriction surjectivity and the following cohomology map

For the native cohomology of an actual short exact sequence of scheme modules,
surjectivity of the map on `Hⁿ` is equivalent to injectivity of the preceding
inclusion on `Hⁿ⁺¹`. In the canonical degree-two problem this gives the exact
criterion needed: `H¹(Ω I_Z)` need not vanish, but its map to `H¹(Ω)` must be
injective. All maps below are the original native derived cohomology maps.
-/

@[expose] public noncomputable section

universe u

namespace M9StacksIntegration.CohomologyRestriction

open CategoryTheory AlgebraicGeometry

/-- In consecutive exact pairs, the first map is surjective precisely when
the last map is injective. -/
theorem surjective_iff_injective_of_exact_neighbors
    {k A B C D : Type*} [Field k]
    [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    [AddCommGroup C] [Module k C] [AddCommGroup D] [Module k D]
    (a : A →ₗ[k] B) (b : B →ₗ[k] C) (c : C →ₗ[k] D)
    (hab : Function.Exact a b) (hbc : Function.Exact b c) :
    Function.Surjective a ↔ Function.Injective c := by
  constructor
  · intro ha x y hxy
    have hz : c (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := (hbc (x - y)).mp hz
    obtain ⟨w, hw⟩ := ha z
    have hbz : b z = 0 := (hab z).mpr ⟨w, hw⟩
    exact sub_eq_zero.mp (hz.symm.trans hbz)
  · intro hc z
    have hcz : c (b z) = 0 := (hbc (b z)).mpr ⟨z, rfl⟩
    have hbz : b z = 0 := hc (by simpa only [map_zero] using hcz)
    exact (hab z).mp hbz

/-- For an actual short exact sequence of sheaves of modules, the original
map on `Hⁿ` is onto exactly when the original inclusion on `Hⁿ⁺¹` is one-to-one.
No properness, finite-dimensionality, or cohomology-vanishing hypothesis is
required. -/
theorem surjective_cohomologyMap_iff_injective_successor
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {S : ShortComplex X.Modules} (hS : S.ShortExact) (n : ℕ) :
    Function.Surjective (cohomologyOverFieldMap k f S.g n) ↔
      Function.Injective (cohomologyOverFieldMap k f S.f (n + 1)) := by
  obtain ⟨d, _hinj, _hfg, hgd, hdf⟩ := exists_cohomologyOverField_longExactSequence k f hS
  exact surjective_iff_injective_of_exact_neighbors
    (cohomologyOverFieldMap k f S.g n).hom (d n).hom
    (cohomologyOverFieldMap k f S.f (n + 1)).hom (hgd n) (hdf n)

end M9StacksIntegration.CohomologyRestriction
