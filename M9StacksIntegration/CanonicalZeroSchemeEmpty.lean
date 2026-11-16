module

public import M9StacksIntegration.ZeroSchemeBaseFieldPoints
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassOfSection

/-!
# Actual native zero schemes and the empty-locus side conditions

The native Chow section zero scheme is literally the checked dual-
evaluation zero ideal. Base-field nonvanishing therefore makes this
actual native scheme empty. The native regular-sequence side condition
then follows vacuously at its actual generic points. No expected
codimension, top-Chern vanishing, or abstract cap rule is an input.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.EmptyZeroSchemeChern

open Stacks.Chow

theorem zeroSchemeOfSection_eq_sectionZeroIdeal {X : Scheme.{u}}
    (E : X.Modules) (s : Γ(E, ⊤)) :
    zeroSchemeOfSection X E s = SectionZeroIdealFactorization.sectionZeroIdeal X E s := rfl

theorem isEmpty_canonical_zeroScheme_of_base_field_pullbacks_ne_zero
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (q : X ⟶ Spec (.of K)) [LocallyOfFiniteType q]
    (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r]
    (s : Γ(E, ⊤))
    (hs : ∀ (p : Spec (.of K) ⟶ X), p ≫ q = 𝟙 _ →
      pullbackGlobalSections p E s ≠ 0) :
    IsEmpty (zeroSchemeOfSection X E s).subscheme :=
  ZeroSchemeBaseFieldPoints.isEmpty_zeroScheme_of_base_field_pullbacks_ne_zero q E r s hs

/-- Actual emptiness supplies the regular-sequence side condition at
actual generic points. No condition is asserted for a nonempty locus. -/
theorem isRegularZeroSchemeSequence_of_isEmpty
    (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S) [LocallyOfFiniteType q]
    (E : X.Modules) (s : Γ(E, ⊤)) (r : ℕ) (m : ℤ)
    [IsEmpty (zeroSchemeOfSection X E s).subscheme] :
    IsRegularZeroSchemeSequence C q E s r m := by
  intro ξ _
  have hFalse : False := isEmptyElim ξ.val
  exact hFalse.elim

theorem isRegularZeroSchemeSequence_of_base_field_pullbacks_ne_zero
    {K : Type u} [Field K] [IsAlgClosed K] (C : ChowSituation.{u})
    {X : Scheme.{u}} (q : X ⟶ Spec (.of K)) [LocallyOfFiniteType q]
    (qC : X ⟶ C.S) [LocallyOfFiniteType qC]
    (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r]
    (s : Γ(E, ⊤)) (m : ℤ)
    (hs : ∀ (p : Spec (.of K) ⟶ X), p ≫ q = 𝟙 _ →
      pullbackGlobalSections p E s ≠ 0) :
    IsRegularZeroSchemeSequence C qC E s r m := by
  letI := isEmpty_canonical_zeroScheme_of_base_field_pullbacks_ne_zero q E r s hs
  exact isRegularZeroSchemeSequence_of_isEmpty C qC E s r m

end M9Native.EmptyZeroSchemeChern
