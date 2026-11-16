module

public import M9StacksIntegration.MukaiParityLinear
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# The actual Yoneda boundary exact sequence in the original scalar action

The boundary is postcomposition with the class of the supplied actual
short exact sequence. Exactness is derived from the native Ext long
exact sequence. No cohomology-boundary identification is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u v w t

namespace M9Native.MukaiYonedaExact

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    (k : Type t) [Field k] [Linear k C] (T : C)

/-- The actual coefficient map on the actual Yoneda Ext group. -/
abbrev coefficientMap {A B : C} (g : A ⟶ B) (n : ℕ) :
    Ext T A n →ₗ[k] Ext T B n :=
  Ext.postcompOfLinear (Ext.mk₀ g) k T (add_zero n)

/-- The actual degree-zero-to-degree-one Yoneda boundary of an actual
short exact sequence, with the original categorical scalar structure. -/
abbrev boundary {S : ShortComplex C} (hS : S.ShortExact) :
    Ext T S.X₃ 0 →ₗ[k] Ext T S.X₁ 1 :=
  Ext.postcompOfLinear hS.extClass k T (zero_add 1)

/-- Exactness at the middle degree-zero Ext group is a native theorem. -/
theorem exact_left {S : ShortComplex C} (hS : S.ShortExact) :
    Function.Exact (coefficientMap k T S.f 0) (coefficientMap k T S.g 0) := by
  have h := Ext.covariant_sequence_exact₂' T hS 0
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

/-- Exactness before the actual Yoneda boundary is a native theorem. -/
theorem exact_middle {S : ShortComplex C} (hS : S.ShortExact) :
    Function.Exact (coefficientMap k T S.g 0) (boundary k T hS) := by
  have h := Ext.covariant_sequence_exact₃' T hS 0 1 (zero_add 1)
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

/-- Exactness after the actual Yoneda boundary is a native theorem. -/
theorem exact_right {S : ShortComplex C} (hS : S.ShortExact) :
    Function.Exact (boundary k T hS) (coefficientMap k T S.f 1) := by
  have h := Ext.covariant_sequence_exact₁' T hS 0 1 (zero_add 1)
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

/-- The first actual coefficient map in degree zero is injective. -/
theorem injective_left {S : ShortComplex C} (hS : S.ShortExact) :
    Function.Injective (coefficientMap k T S.f 0) := by
  let : Mono S.f := hS.mono_f
  exact Ext.postcomp_mk₀_injective_of_mono T S.f

/-- The checked finite exact-sequence dimension formula now applies to
the actual native Ext boundary, with no supplied exactness premise. -/
theorem finrank_Ext0_add_boundary_range {S : ShortComplex C} (hS : S.ShortExact)
    [Module.Finite k (Ext T S.X₂ 0)] [Module.Finite k (Ext T S.X₃ 0)] :
    Module.finrank k (Ext T S.X₂ 0) + Module.finrank k (LinearMap.range (boundary k T hS)) =
      Module.finrank k (Ext T S.X₁ 0) + Module.finrank k (Ext T S.X₃ 0) :=
  MukaiParityLinear.finrank_add_range_eq
    (coefficientMap k T S.f 0) (coefficientMap k T S.g 0) (boundary k T hS)
    (injective_left k T hS) (exact_left k T hS) (exact_middle k T hS)

end M9Native.MukaiYonedaExact
