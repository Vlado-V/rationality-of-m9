module

public import M9StacksIntegration.ChowLineProperPush
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.Induction

/-!
# Genuine fundamental pushforward of a regular zero section

The zero scheme is the literal native dual-evaluation ideal, including
its scheme structure. Stacks 0FA9 and native closed-immersion cycle
pushforward prove its actual fundamental-class identity. The inputs are
the genuine dimension and regular-stalk-sequence hypotheses, never a
Chow identity or a set-theoretic zero-locus comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.Chow Stacks.Chow.GenuineChern

universe u

namespace M9Native.ChowRegularSectionClass

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
  [LocallyOfFiniteType q] (F : X.Modules) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r] (s : Γ(F,⊤))

/-- The native closed-zero cycle in the original ambient Chow group is the genuine top cap. -/
theorem closed_zeroClass_eq_topCap (n : ℤ)
    (hX : schemeDeltaDimension C q ≤ (n : EInt))
    (hZ : schemeDeltaDimension C ((zeroSchemeOfSection X F s).subschemeι ≫ q) ≤
      ((n-(r:ℤ) : ℤ) : EInt))
    (hreg : IsRegularZeroSchemeSequence C q F s r (n-(r:ℤ))) :
    QuotientAddGroup.mk' (rationalEquivalences C q (n-(r:ℤ)))
        (cycleAssociatedToClosedSubscheme C q (zeroSchemeOfSection X F s).subschemeι
          (n-(r:ℤ))) =
      chernCap C r q F n (Fin.last r) (fundamentalChowClass C q n) := by
  exact (SectionZeroScheme.reducedTopChernCap C r q F s n hX hZ hreg).symm

/-- The actual own fundamental class of the FULL zero scheme pushes to the actual top Chern cap. -/
theorem inclusionPush_fundamental_eq_topCap (n : ℤ)
    (hX : schemeDeltaDimension C q ≤ (n : EInt))
    (hZ : schemeDeltaDimension C ((zeroSchemeOfSection X F s).subschemeι ≫ q) ≤
      ((n-(r:ℤ) : ℤ) : EInt))
    (hreg : IsRegularZeroSchemeSequence C q F s r (n-(r:ℤ))) :
    ChowLineProperPush.properPush C ((zeroSchemeOfSection X F s).subschemeι ≫ q) q
      (zeroSchemeOfSection X F s).subschemeι rfl (n-(r:ℤ))
      (fundamentalChowClass C ((zeroSchemeOfSection X F s).subschemeι ≫ q) (n-(r:ℤ))) =
      chernCap C r q F n (Fin.last r) (fundamentalChowClass C q n) := by
  have h := closed_zeroClass_eq_topCap C q F r s n hX hZ hreg
  simpa only [ChowLineProperPush.properPush, fundamentalChowClass, fundamentalCycle,
    properChowPushforward_mk, properPushforward_cycleAssociatedToClosedSubscheme_id] using h

section Composition

variable {A B T : Scheme.{u}} (qA : A ⟶ C.S) [LocallyOfFiniteType qA]
  (qB : B ⟶ C.S) [LocallyOfFiniteType qB] (qT : T ⟶ C.S) [LocallyOfFiniteType qT]
  (i : A ⟶ B) [IsProper i] (p : B ⟶ T) [IsProper p]
  (hi : i ≫ qB=qA) (hp : p ≫ qT=qB)

/-- Literal genuine proper pushforward composition, with factorization supplied by actual properness. -/
theorem properPush_comp_apply (k : ℤ) (α : chowGroup C qA k) :
    ChowLineProperPush.properPush C qB qT p hp k
      (ChowLineProperPush.properPush C qA qB i hi k α) =
    ChowLineProperPush.properPush C qA qT (i ≫ p)
      (by rw [Category.assoc, hp, hi]) k α := by
  exact congrArg (fun f : chowGroup C qA k →+ chowGroup C qT k => f α)
    (properChowPushforward_comp C qA qB qT i p hi hp k
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C qA qB i hi k)
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C qB qT p hp k))

end Composition

end M9Native.ChowRegularSectionClass
