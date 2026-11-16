module

public import M9StacksIntegration.GradedCapVirtualSchur
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.WhitneyInvertible

/-!
# Removing an actual unit subline from integral Chow Chern families

The genuine fixed-point restriction jets have orientation
O → F_(j+1) → F_j. The native unit-subbundle Whitney formula removes
that actual subline without reversing or splitting the extension.
Formal inversion then removes it from the actual virtual operators.
This is separate from the quotient-unit rows used for E18/E10.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Chow Stacks.Chow.GenuineChern

universe u

namespace M9Native.ChowChernUnitSubrows

open GradedCapVirtualSchur

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (q : X ⟶ C.S)
  [LocallyOfFiniteType q] (S : ShortComplex X.Modules) (hS : S.ShortExact)
  (e : S.X₁ ≅ SheafOfModules.unit X.ringCatSheaf) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₂ (r+1)]
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₃ r]

include hS e

/-- The original native unit-subline theorem, in the actual jet-row
orientation and with no splitting premise. -/
theorem chernFamily_eq :
    chernFamily C q S.X₂ (r+1) = chernFamily C q S.X₃ r :=
  chernFamily_eq_of_shortExact_of_iso_unit C q S hS e r

/-- The actual recursively constructed inverse families also agree. -/
theorem inverseFamily_eq :
    inverseFamily C q S.X₂ (r+1) = inverseFamily C q S.X₃ r := by
  rw [inverseFamily_eq_gradedRightInv, inverseFamily_eq_gradedRightInv,
    chernFamily_eq C q S hS e r]

/-- Actual unit sublines can be removed from the virtual denominator
without changing the genuine factor order. -/
theorem virtualFamily_denominator_eq (F : X.Modules) (s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F s] :
    virtualFamily C q F S.X₂ s (r+1) = virtualFamily C q F S.X₃ s r := by
  rw [virtualFamily, virtualFamily, inverseFamily_eq C q S hS e r]

/-- In particular the fixed-point jet rows remove actual unit
sublines from the numerator F as they are geometrically oriented. -/
theorem virtualFamily_numerator_eq (E : X.Modules) (s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E s] :
    virtualFamily C q S.X₂ E (r+1) s = virtualFamily C q S.X₃ E r s := by
  rw [virtualFamily, virtualFamily, chernFamily_eq C q S hS e r]

end M9Native.ChowChernUnitSubrows
