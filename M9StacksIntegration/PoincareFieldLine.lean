module

public import Mathlib.Algebra.Category.ModuleCat.Simple
public import Mathlib.CategoryTheory.Preadditive.Schur
public import StacksFrontier.AlgebraicGeometry.Modules.SpecFieldModules

/-!
# Actual line modules on the spectrum of a field

The native equivalence between modules over a field and sheaves of
modules on its actual spectrum makes the structure sheaf a simple
object.  Consequently a nonzero map from a line is injective and a
nonzero map to a line is surjective.  The line is identified with the
structure sheaf by an actual module isomorphism; no replacement of
the spectrum or of its sheaf category is made.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace M9Native.PoincareChern

/-- The actual structure sheaf of `Spec K` is a simple object of its
actual category of sheaves of modules. -/
theorem specFieldUnit_simple (K : Type u) [Field K] :
    Simple (C := (Spec (.of K)).Modules)
      (SheafOfModules.unit (Spec (.of K)).ringCatSheaf) := by
  letI : (tilde.functor (.of K)).IsEquivalence :=
    SpecField.isEquivalence_tildeFunctor (Field.toIsField K)
  have hs : Simple ((tilde.functor (.of K)).obj
      (ModuleCat.of (CommRingCat.of K) (CommRingCat.of K))) :=
    simple_obj (tilde.functor (.of K))
      (ModuleCat.of (CommRingCat.of K) (CommRingCat.of K))
  exact @Simple.of_iso (Spec (.of K)).Modules _ _ _ _ hs
    (tildeSelf (R := .of K)).symm

/-- An actual line trivialization transports simplicity on `Spec K`. -/
theorem specFieldLine_simple (K : Type u) [Field K]
    {N : (Spec (.of K)).Modules}
    (e : N ≅ SheafOfModules.unit (Spec (.of K)).ringCatSheaf) : Simple N := by
  haveI := specFieldUnit_simple K
  exact Simple.of_iso e

/-- A nonzero map from an actual line over `Spec K` is monomorphic. -/
theorem mono_from_specFieldLine_of_ne_zero (K : Type u) [Field K]
    {N Q : (Spec (.of K)).Modules}
    (e : N ≅ SheafOfModules.unit (Spec (.of K)).ringCatSheaf)
    (φ : N ⟶ Q) (hφ : φ ≠ 0) : Mono φ := by
  haveI := specFieldLine_simple K e
  exact mono_of_nonzero_from_simple hφ

/-- A nonzero map to an actual line over `Spec K` is epimorphic. -/
theorem epi_to_specFieldLine_of_ne_zero (K : Type u) [Field K]
    {N Q : (Spec (.of K)).Modules}
    (e : N ≅ SheafOfModules.unit (Spec (.of K)).ringCatSheaf)
    (φ : Q ⟶ N) (hφ : φ ≠ 0) : Epi φ := by
  haveI := specFieldLine_simple K e
  exact epi_of_nonzero_to_simple hφ

end M9Native.PoincareChern
