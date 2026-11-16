module

public import M9StacksIntegration.LineSectionIdealOperations

/-! A genuinely zero pulled section contributes the zero ideal to
the FULL section ideal sum. The comparison retains all scheme
structure and applies to every actual scheme pullback. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace M9Native.LineSectionZeroRowDrop

variable {X : Scheme.{u}} (L : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

theorem zeroSection_ideal_eq_bot :
    Stacks.Divisors.zeroScheme X L (0 : Γ(L, ⊤)) = ⊥ := by
  apply bot_unique
  have h := (factorsThrough_ideal_iff_ideal_le_ker _ (𝟙 X)).mp
    ((Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme X L
      (0 : Γ(L, ⊤)) (𝟙 X)).mp (map_zero _))
  simpa only [Scheme.Hom.ker_eq_bot_of_isIso] using h

/-- A zero actual first row can be removed from the full pulled ideal
sum, without passing to supports or reducing the remaining ideal. -/
theorem ideal_comap_eq_tail_of_head_zero {Y : Scheme.{u}} (f : Y ⟶ X)
    (s : Γ(L, ⊤)) (ss : List Γ(L, ⊤))
    (hs : pullbackGlobalSections f L s = 0) :
    (LineSectionIdealSum.ideal L (s :: ss)).comap f =
      LineSectionIdealSum.ideal ((Scheme.Modules.pullback f).obj L)
        (ss.map (pullbackGlobalSections f L)) := by
  rw [LineSectionIdealOperations.ideal_comap, List.map_cons,
    LineSectionIdealOperations.ideal_cons, hs, zeroSection_ideal_eq_bot, bot_sup_eq]

end M9Native.LineSectionZeroRowDrop
