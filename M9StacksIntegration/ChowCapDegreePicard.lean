module

public import M9StacksIntegration.CartierCapDegreeRestriction
public import M9StacksIntegration.ChowPicardCapTransport

/-!
# Actual finite Picard cap-degree pairings and the literal word functional

The finite family uses the actual native representatives of the actual
Picard classes. Replacing those representatives by isomorphic actual
modules preserves the native cap-degree map.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.ChowCapDegreePicard

open Stacks.Chow ChowCapDegree ChowCapWords CurveTopChowClass CurvePowerChowFunctional

attribute [local instance] ChowCapDegree.isInvertible_sheaf_of_presheaf

theorem chosenLine_isInvertible {X : Scheme.{u}} (x : Stacks.Picard.ofScheme X) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (chosenLine x).1 :=
  (chosenLine x).2

attribute [local instance] chosenLine_isInvertible

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

def capDegreePicard {d : ℕ} (x : Fin d → Stacks.Picard.ofScheme X) :
    chowGroup (fieldChowSituation k) f d →+ ℤ :=
  @capDegree k _ X f _ d (fun j => (chosenLine (x j)).1)
    (fun j => chosenLine_isInvertible (x j))

theorem capDegree_congr_iso {d : ℕ} (L M : Fin d → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)]
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M j)]
    (e : ∀ j, Nonempty (L j ≅ M j)) : capDegree k f L = capDegree k f M := by
  apply AddMonoidHom.ext
  intro a
  simp only [capDegree, iteratedFirstChernCap, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  apply congrArg (chowDegree (fieldChowSituation k)
    (fieldChowSituation_dimensionFunction_eq_zero k) f (IsLocalRing.closedPoint k))
  apply iteratedChernCapOnChow_congr_forall₂ (fieldChowSituation k) f
    (forall₂_ofFn fun j m z => invCap_congr (fieldChowSituation k) f (L j) (M j)
      (Classical.choice (e j)) m z)
  exact (chowGroupCast_heq (fieldChowSituation k) f _ a).trans
    (chowGroupCast_heq (fieldChowSituation k) f _ a).symm

theorem nonempty_chosenLine_class_iso {Y : Scheme.{u}} (L : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatIsSheaf L) :
    Nonempty ((chosenLine
      (Stacks.SheafOfModules.picardClass Y.presheaf Y.ringCatIsSheaf L hL)).1 ≅ L) := by
  let x := Stacks.SheafOfModules.picardClass Y.presheaf Y.ringCatIsSheaf L hL
  have h : Stacks.SheafOfModules.picardClass Y.presheaf Y.ringCatIsSheaf
      (chosenLine x).1 (chosenLine x).2 = x :=
    Stacks.Picard.classOf_picardRepresentative Y.toRingedSpace x
  exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).mp h

theorem capDegreePicard_classes {d : ℕ} (L : Fin d → X.Modules)
    [hL : ∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    capDegreePicard k f (fun j => Stacks.SheafOfModules.picardClass
      X.presheaf X.ringCatIsSheaf (L j) (hL j)) = capDegree k f L := by
  apply capDegree_congr_iso
  intro j
  exact nonempty_chosenLine_class_iso (L j) (hL j)

theorem nonempty_chosenLine_pullback_iso {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (x : Stacks.Picard.ofScheme Z) :
    Nonempty ((chosenLine (Stacks.Picard.schemePullbackClass g x)).1 ≅
      (Scheme.Modules.pullback g).obj (chosenLine x).1) := by
  let P := ChowPicardCapTransport.pullbackLine g (chosenLine x)
  have h := Stacks.Picard.pullbackClass_classOf g.toLRSHom.toShHom
    (chosenLine x).1 (chosenLine x).2
  have hx : Stacks.SheafOfModules.picardClass Z.presheaf Z.ringCatIsSheaf
      (chosenLine x).1 (chosenLine x).2 = x :=
    Stacks.Picard.classOf_picardRepresentative Z.toRingedSpace x
  rw [hx] at h
  have hp : Stacks.Picard.schemePullbackClass g x =
      Stacks.SheafOfModules.picardClass Y.presheaf Y.ringCatIsSheaf P.1 P.2 := h
  rw [hp]
  exact nonempty_chosenLine_class_iso P.1 P.2

theorem wordDegree_eq_capDegreePicard (xs : List (Stacks.Picard.ofScheme X)) :
    wordDegree k f (xs.map chosenLine) =
      capDegreePicard k f (fun j : Fin xs.length => xs.get j)
        (identityChowClass (fieldChowSituation k) f xs.length) := by
  let C := fieldChowSituation k
  have hget : List.ofFn (fun j : Fin xs.length => xs.get j) = xs := List.ofFn_get xs
  have hOps : List.ofFn (fun j : Fin xs.length =>
      invCap C f (chosenLine (xs.get j)).1) = (xs.map chosenLine).map (lineCap C f) := by
    have h := congrArg (fun ys : List (Stacks.Picard.ofScheme X) =>
      ys.map (fun x => lineCap C f (chosenLine x))) hget
    simpa only [List.map_ofFn, List.map_map, Function.comp_def, lineCap] using h
  unfold wordDegree capDegreePicard capDegree iteratedFirstChernCap
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  apply congrArg (chowDegree C (fieldChowSituation_dimensionFunction_eq_zero k) f
    (IsLocalRing.closedPoint k))
  apply chowGroup_eq_of_heq C f
  apply HEq.symm
  apply iteratedChernCapOnChow_heq_of_eq C f hOps 0
  have hd : (xs.length : ℤ) =
      0 + (((xs.map chosenLine).map (lineCap C f)).length : ℤ) := by simp
  have hh : ∀ a b : ℤ, a = b → HEq (identityChowClass C f a) (identityChowClass C f b) := by
    rintro a b rfl
    rfl
  exact (chowGroupCast_heq C f _ (identityChowClass C f xs.length)).trans (hh _ _ hd)

end M9Native.ChowCapDegreePicard
