module

public import M9StacksIntegration.CartierDivisorChernCap
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.Proper
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme

/-!
# The actual Cartier cap as pushforward from the original closed immersion

The source of the original immersion is compared with its actual
scheme-theoretic image using the proved image isomorphism. This retains
the original graph morphism in the cap restriction formula.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.ClosedImmersionChernCap

open Stacks.Chow CurveTopChowClass

variable (C : ChowSituation.{u}) {X Z : Scheme.{u}} (f : X ⟶ C.S)
  [LocallyOfFiniteType f] (i : Z ⟶ X) [IsClosedImmersion i]

theorem closedSubschemeCycle_eq_image (d : ℤ) :
    cycleAssociatedToClosedSubscheme C f i d =
      cycleAssociatedToClosedSubscheme C f i.ker.subschemeι d := by
  let : IsIso i.toImage := IsClosedImmersion.isIso_of_ker_eq i i.imageι i.toImage
    i.toImage_imageι (Scheme.IdealSheafData.ker_subschemeι i.ker).symm
  exact cycleAssociatedToClosedSubscheme_eq_of_iso C f i i.ker.subschemeι
    (asIso i.toImage) i.toImage_imageι d

theorem pushforward_identityChowClass (d : ℤ) :
    properChowPushforward C (i ≫ f) f i rfl d
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C (i ≫ f) f i rfl d)
        (identityChowClass C (i ≫ f) d) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C f i d) := by
  rw [identityChowClass, properChowPushforward_mk]
  apply congrArg (QuotientAddGroup.mk' (rationalEquivalences C f d))
  simpa only [Category.id_comp] using
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      (i ≫ f) f i rfl (𝟙 Z) d

theorem invCap_fundamental_eq_pushforward [IsIntegral X] (n : ℤ)
    (hn : schemeDeltaDimension C f = (n : EInt))
    [hD : Stacks.Divisors.IsEffectiveCartierDivisor i.ker] :
    letI := Stacks.Divisors.isInvertible_invertibleSheaf_picard i.ker
    (invCap C f (Stacks.Divisors.modulesInvertibleSheaf i.ker)).capOnChow C f (n - 1)
        (identityChowClass C f (n - 1 + 1)) =
      properChowPushforward C (i ≫ f) f i rfl (n - 1)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C (i ≫ f) f i rfl
          (n - 1)) (identityChowClass C (i ≫ f) (n - 1)) := by
  rw [CartierDivisorChernCap.invCap_fundamental_divisor C f n hn i.ker,
    pushforward_identityChowClass C f i (n - 1), closedSubschemeCycle_eq_image C f i (n - 1)]

end M9Native.ClosedImmersionChernCap
