module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer.GlobalSections
public import Mathlib.Tactic

/-!
# Actual unit-to-sheaf morphisms and pullback of their global sections

The section represented by a morphism `O_X → M` is its value on the
actual global unit. This detects the zero morphism. Pulling back the
section agrees with pulling back the morphism and inserting the actual
structure-sheaf pullback isomorphism. These are the native sheaf/global-
section identifications needed for the curried incidence Hom section.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.Ample (unitModule)

universe u

namespace M9Native.UnitSectionPullback

/-- The actual global section defined by an actual structure-sheaf
morphism, obtained by evaluating it on the global unit. -/
def unitSection {X : Scheme.{u}} {M : X.Modules} (a : unitModule X ⟶ M) : Γ(M, ⊤) :=
  a.app ⊤ (1 : Γ(X, ⊤))

/-- An actual sheaf morphism out of the structure sheaf is determined
by its value on the actual global unit. -/
theorem eq_zero_of_unitSection_eq_zero {X : Scheme.{u}} {M : X.Modules}
    (a : unitModule X ⟶ M) (ha : unitSection a = 0) : a = 0 := by
  ext U r
  have hnat := a.mapPresheaf.naturality (homOfLE (show U ≤ ⊤ from le_top)).op
  have h1 : a.app U (1 : Γ(X, U)) = 0 := by
    have h := ConcreteCategory.congr_hom hnat (1 : Γ(X, ⊤))
    have hres : (unitModule X).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (1 : Γ(X, ⊤)) = (1 : Γ(X, U)) := by
      change X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (1 : Γ(X, ⊤)) = 1
      exact map_one _
    change a.app U ((unitModule X).presheaf.map
        (homOfLE (show U ≤ ⊤ from le_top)).op (1 : Γ(X, ⊤))) =
      M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (unitSection a) at h
    rw [hres, ha, map_zero] at h
    exact h
  change a.app U r = 0
  let c : Γ(X, U) := r
  calc
    a.app U r = a.app U (c • (1 : Γ(X, U))) := by
      exact congrArg (fun z : Γ(X, U) => a.app U z) (mul_one c).symm
    _ = c • a.app U (1 : Γ(X, U)) :=
      (a.val.app (op U)).hom.map_smul c (1 : Γ(X, U))
    _ = 0 := by rw [h1, smul_zero]

/-- The actual pulled-back unit-to-sheaf morphism. -/
def pulledUnitMap {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    (a : unitModule Y ⟶ M) : unitModule X ⟶ (Scheme.Modules.pullback f).obj M :=
  (Scheme.Modules.pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map a

theorem pullback_unit_one {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullbackUnitIso f).inv.app ⊤ (1 : Γ(X, ⊤)) =
      pullbackGlobalSections f (unitModule Y) (1 : Γ(Y, ⊤)) := by
  let e := Scheme.Modules.pullbackUnitIso f
  let t := pullbackGlobalSections f (unitModule Y) (1 : Γ(Y, ⊤))
  have h := congrArg (fun z : Γ(X, ⊤) => e.inv.app ⊤ z)
    (SectionsEqualizer.pullbackUnitIso_unit f (1 : Γ(Y, ⊤)))
  rw [map_one] at h
  have hc : e.inv.app ⊤ (e.hom.app ⊤ t) = t :=
    SectionsEqualizer.moduleIso_hom_inv_app e.symm t
  exact (hc.symm.trans h).symm

/-- Actual pullback of the actual unit-defined global section. -/
theorem unitSection_pulledUnitMap {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    (a : unitModule Y ⟶ M) :
    unitSection (pulledUnitMap f a) = pullbackGlobalSections f M (unitSection a) := by
  change ((Scheme.Modules.pullback f).map a).app ⊤
    ((Scheme.Modules.pullbackUnitIso f).inv.app ⊤ (1 : Γ(X, ⊤))) = _
  rw [pullback_unit_one]
  exact (Stacks.AlgebraicGeometry.IdealOfClosedSubscheme.pullbackGlobalSections_naturality
    f a (1 : Γ(Y, ⊤))).symm

/-- A nonzero actual pulled-back unit morphism gives a nonzero
pulled-back global section. -/
theorem pullback_unitSection_ne_zero {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    (a : unitModule Y ⟶ M) (ha : pulledUnitMap f a ≠ 0) :
    pullbackGlobalSections f M (unitSection a) ≠ 0 := by
  intro hs
  apply ha
  apply eq_zero_of_unitSection_eq_zero
  exact (unitSection_pulledUnitMap f a).trans hs

end M9Native.UnitSectionPullback
