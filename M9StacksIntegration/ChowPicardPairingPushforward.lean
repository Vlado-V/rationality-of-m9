module

public import M9StacksIntegration.CurvePowerPointCapDegree

/-!
# Actual Picard pairings under proper maps and isomorphisms

The proper projection formula acts on every actual Chow class. For an
actual isomorphism its pushforward carries the original fundamental
class to the target fundamental class. No intersection number or
numerical equality is supplied as an assumption.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.ChowPicardPairingPushforward

open Stacks.Chow CurveTopChowClass ChowCapDegreePicard CurvePowerChowFunctional

attribute [local instance] ChowCapDegreePicard.chosenLine_isInvertible

theorem capDegreePicard_proper (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (fY : Y ⟶ Spec (.of k)) [IsProper fY]
    (g : Y ⟶ X) [IsProper g] (hg : g ≫ f = fY)
    {m : ℕ} (x : Fin m → Stacks.Picard.ofScheme X)
    (a : chowGroup (fieldChowSituation k) fY m) :
    capDegreePicard k fY (fun j => Stacks.Picard.schemePullbackClass g (x j)) a =
      capDegreePicard k f x
        (properChowPushforward (fieldChowSituation k) fY f g hg m
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper
            (fieldChowSituation k) fY f g hg m) a) := by
  rw [PicardCartierCapDegreeRestriction.capDegreePicard_pullback_eq]
  exact ChowCapDegree.capDegree_properChowPushforward k f fY g hg
    (fun j => (chosenLine (x j)).1) a

theorem pushforward_identityChowClass_of_isIso (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (i : Y ⟶ X) [IsIso i] (d : ℤ) :
    properChowPushforward C (i ≫ f) f i rfl d
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C (i ≫ f) f i rfl d)
        (identityChowClass C (i ≫ f) d) = identityChowClass C f d := by
  rw [ClosedImmersionChernCap.pushforward_identityChowClass C f i d]
  apply congrArg (QuotientAddGroup.mk' (rationalEquivalences C f d))
  exact cycleAssociatedToClosedSubscheme_eq_of_iso C f i (𝟙 X)
    (asIso i) (Category.comp_id i) d

theorem capDegreePicard_isIso (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (i : Y ⟶ X) [IsIso i]
    {m : ℕ} (x : Fin m → Stacks.Picard.ofScheme X) :
    capDegreePicard k (i ≫ f) (fun j => Stacks.Picard.schemePullbackClass i (x j))
        (identityChowClass (fieldChowSituation k) (i ≫ f) m) =
      capDegreePicard k f x (identityChowClass (fieldChowSituation k) f m) := by
  exact (capDegreePicard_proper k f (i ≫ f) i rfl x
    (identityChowClass (fieldChowSituation k) (i ≫ f) m)).trans
      (congrArg (capDegreePicard k f x)
        (pushforward_identityChowClass_of_isIso (fieldChowSituation k) f i m))

theorem capDegreePicard_isIso_over (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (fY : Y ⟶ Spec (.of k)) [IsProper fY]
    (i : Y ⟶ X) [IsIso i] (hi : i ≫ f = fY)
    {m : ℕ} (x : Fin m → Stacks.Picard.ofScheme X) :
    capDegreePicard k fY (fun j => Stacks.Picard.schemePullbackClass i (x j))
        (identityChowClass (fieldChowSituation k) fY m) =
      capDegreePicard k f x (identityChowClass (fieldChowSituation k) f m) := by
  exact (CurvePowerPointCapDegree.capValue_structure_congr k fY (i ≫ f) hi.symm _).trans
    (capDegreePicard_isIso k f i x)

end M9Native.ChowPicardPairingPushforward
