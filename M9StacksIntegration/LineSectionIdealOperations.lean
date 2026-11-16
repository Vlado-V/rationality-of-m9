module

public import M9StacksIntegration.LineSectionIdealSum
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic

/-! Finite actual line-section ideal sums retain their full scheme
structure under list splitting and arbitrary scheme pullback. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace M9Native.LineSectionIdealOperations
variable {X : Scheme.{u}} (L : X.Modules)
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

theorem ideal_nil : LineSectionIdealSum.ideal L [] = ⊥ := by
  simp [LineSectionIdealSum.ideal]

theorem ideal_cons (s : Γ(L, ⊤)) (ss : List Γ(L, ⊤)) :
    LineSectionIdealSum.ideal L (s :: ss) =
      Stacks.Divisors.zeroScheme X L s ⊔ LineSectionIdealSum.ideal L ss := by
  apply le_antisymm
  · refine iSup_le fun z => ?_
    rcases List.mem_cons.mp z.2 with h | h
    · change Stacks.Divisors.zeroScheme X L z.1 ≤ _
      rw [h]
      exact le_sup_left
    · exact le_trans (le_iSup_of_le ⟨z.1, h⟩ le_rfl) le_sup_right
  · refine sup_le ?_ (iSup_le fun z => ?_)
    · exact le_iSup_of_le ⟨s, List.mem_cons_self⟩ le_rfl
    · exact le_iSup_of_le ⟨z.1, List.mem_cons_of_mem s z.2⟩ le_rfl

/-- Pullback of the FULL ideal sum is the FULL ideal sum of the actual
pulled-back sections of the actual pulled-back line. -/
theorem ideal_comap {Y : Scheme.{u}} (f : Y ⟶ X) (ss : List Γ(L, ⊤)) :
    (LineSectionIdealSum.ideal L ss).comap f =
      LineSectionIdealSum.ideal ((Scheme.Modules.pullback f).obj L)
        (ss.map (pullbackGlobalSections f L)) := by
  induction ss with
  | nil => rw [ideal_nil, Scheme.IdealSheafData.comap_bot, List.map_nil, ideal_nil]
  | cons s ss ih =>
    rw [ideal_cons, Scheme.IdealSheafData.comap_sup, ih,
      ← Stacks.Divisors.zeroScheme_pullback, List.map_cons, ideal_cons]

theorem tupleIdeal_comap {Y : Scheme.{u}} (f : Y ⟶ X) {n : ℕ} (s : Fin n → Γ(L, ⊤)) :
    (LineSectionIdealSum.ideal L (List.ofFn s)).comap f =
      LineSectionIdealSum.ideal ((Scheme.Modules.pullback f).obj L)
        (List.ofFn (fun i => pullbackGlobalSections f L (s i))) := by
  simpa only [List.map_ofFn, Function.comp_def] using ideal_comap L f (List.ofFn s)

end M9Native.LineSectionIdealOperations
