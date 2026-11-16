module

public import StacksFrontier.AlgebraicGeometry.Recovery27.PullbackFreeIso
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# A constant map pulls a vector bundle back to a free bundle

A singleton topological image is contained in one actual local
trivialization of the bundle. The original scheme morphism lifts to that
open, and the native pullback and restriction isomorphisms transport the
trivialization. No residue-field factorization, reducedness, or chosen
trivialization of the pulled bundle is an input.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.ConstantMapPullback

theorem nonempty_pullback_iso_free {X Y : Scheme.{u}} (g : X ⟶ Y)
    (E : Y.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r]
    (hc : ∃ y : Y, ∀ x : X, g.base x = y) :
    Nonempty ((Scheme.Modules.pullback g).obj E ≅
      SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))) := by
  obtain ⟨y, hy⟩ := hc
  obtain ⟨U, hyU, ⟨e⟩⟩ :=
    (Scheme.Modules.isFiniteLocallyFreeOfRank_iff E r).mpr inferInstance y
  have hrange : Set.range g.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    rw [hy x]
    exact hyU
  let a : X ⟶ U.toScheme := IsOpenImmersion.lift U.ι g hrange
  have ha : a ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
  exact ⟨(Scheme.Modules.pullbackCongr ha).symm.app E ≪≫
    (Scheme.Modules.pullbackComp a U.ι).symm.app E ≪≫
    (Scheme.Modules.pullback a).mapIso
      (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app E).symm ≪≫ e) ≪≫
    AlgebraicGeometry.Grassmannian.pullbackFreeIso a r⟩

def free_rank_one_iso_unit (X : Scheme.{u}) :
    (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 1)) : X.Modules) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  coproductUniqueIso (fun _ : ULift.{u} (Fin 1) => SheafOfModules.unit X.ringCatSheaf)

theorem nonempty_pullback_line_iso_unit {X Y : Scheme.{u}} (g : X ⟶ Y)
    (L : Y.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1]
    (hc : ∃ y : Y, ∀ x : X, g.base x = y) :
    Nonempty ((Scheme.Modules.pullback g).obj L ≅ SheafOfModules.unit X.ringCatSheaf) := by
  obtain ⟨e⟩ := nonempty_pullback_iso_free g L 1 hc
  exact ⟨e ≪≫ free_rank_one_iso_unit X⟩

end M9Native.ConstantMapPullback
