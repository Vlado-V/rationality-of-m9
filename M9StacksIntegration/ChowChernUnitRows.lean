module

public import M9StacksIntegration.GradedCapVirtualSchur
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.WhitneySum

/-!
# Removing actual unit quotients from genuine Chow Chern families

An actual short exact row A → B → L with an actual isomorphism L ≅ O
has c(B)=c(A) by the unconditional native Whitney formula. Consequently
the actual inverse and virtual families agree as well. These lemmas
apply to the ordinary fixed-jet rows in the direct C9 construction;
their repetition removes the eight actual unit quotients between the
rank-ten and rank-eighteen bundles. No K-zero-to-Chow realization or
Chern-family equality is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Chow Stacks.Chow.GenuineChern

universe u

namespace M9Native.ChowChernUnitRows

open GradedCapVirtualSchur

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
  [LocallyOfFiniteType q] (S : ShortComplex X.Modules) (hS : S.ShortExact)
  (e : S.X₃ ≅ SheafOfModules.unit X.ringCatSheaf) (r : ℕ)
  [hA : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₁ r]
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₂ (r+1)]

include hS e

/-- A genuine unit quotient contributes the actual unit Chern family,
so Whitney removes it on every integral Chow group at once. -/
theorem chernFamily_eq :
    chernFamily C q S.X₂ (r+1) = chernFamily C q S.X₁ r := by
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₃ 1 :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e.symm
      (isFiniteLocallyFreeOfRank_one_of_isInvertible _)
  rw [chernFamily_eq_mul_of_shortExact C q S hS r 1,
    chernFamily_eq_one_of_iso_unit C q S.X₃ e, mul_one]

/-- Equality of the genuine Chern families gives equality of their
actual recursively constructed inverse cap families. -/
theorem inverseFamily_eq :
    inverseFamily C q S.X₂ (r+1) = inverseFamily C q S.X₁ r := by
  rw [inverseFamily_eq_gradedRightInv, inverseFamily_eq_gradedRightInv,
    chernFamily_eq C q S hS e r]

/-- Removing an actual unit quotient from the denominator preserves
the actual virtual family, with the original factor order. -/
theorem virtualFamily_denominator_eq (F : X.Modules) (s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F s] :
    virtualFamily C q F S.X₂ s (r+1) = virtualFamily C q F S.X₁ s r := by
  rw [virtualFamily, virtualFamily, inverseFamily_eq C q S hS e r]

/-- The analogous numerator reduction also follows directly from the
same actual row; no commutation of cap operators is required. -/
theorem virtualFamily_numerator_eq (E : X.Modules) (s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E s] :
    virtualFamily C q S.X₂ E (r+1) s = virtualFamily C q S.X₁ E r s := by
  rw [virtualFamily, virtualFamily, chernFamily_eq C q S hS e r]

end M9Native.ChowChernUnitRows
