module

public import M9StacksIntegration.CurveEtaleRationalFibre
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.EtaleRationalPoints
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange

/-!
# Point count of the constructed rational étale fibre

The original curve map constructs its rational étale fibre. Actual finite
locally free rank is preserved by the literal pullback square, and the
native finite étale point count gives the number of its original-field
sections. The rank is a genuine generic intermediate; applications must
derive it from the original map and line degree.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.CurveEtaleRationalFibre

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of K)) (fY : Y ⟶ Spec (.of K))
  [IsCurve K fX] [IsCurve K fY] [IsProper fX] [IsProper fY]
  [Smooth fX] [Smooth fY]
  (g : X ⟶ Y) (hg : g ≫ fY = fX)
  (hnc : ¬ ∃ y : Y, ∀ x : X, g.base x = y)

include hg hnc

/-- The full fibre has exactly the actual native finite-flat rank many
distinct original-field sections; the fibre and its étaleness are derived. -/
theorem exists_fibre_card (r : ℕ) [Stacks.Morphisms.IsFiniteLocallyFreeOfRank g r] :
    ∃ q : Spec (.of K) ⟶ Y, q ≫ fY = 𝟙 _ ∧
      Etale (pullback.snd g q) ∧
      Nat.card {p : Spec (.of K) ⟶ pullback g q // p ≫ pullback.snd g q = 𝟙 _} = r := by
  obtain ⟨q,hq,he⟩ := exists_etale_fibre K fX fY g hg hnc
  let := he
  let : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.snd g q) r :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
      (IsPullback.of_hasPullback g q)
  exact ⟨q,hq,he,nat_card_sections_eq_of_etale_of_isFiniteLocallyFreeOfRank K
    (pullback g q) (pullback.snd g q) r⟩

end M9Native.CurveEtaleRationalFibre
