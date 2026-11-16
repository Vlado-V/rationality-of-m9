module

public import M9StacksIntegration.CurvePowerChowFunctional

/-!
# The actual first Chern cap as a homomorphism out of the Picard group

The representative is the native actual invertible module. Isomorphic
representatives give the same native cap and the native tensor formula
proves additivity on every actual Chow class. The descent proof follows
the native curve Picard-to-Chow construction, without restricting the
input Chow class to the fundamental class of a curve.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.ChowPicardCap

open Stacks.Chow ChowCapWords CurvePowerChowFunctional

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
  [LocallyOfFiniteType f] (d : ℤ)

def capFun (x : Stacks.Picard.ofScheme X) : chowGroup C f (d + 1) →+ chowGroup C f d :=
  (lineCap C f (chosenLine x)).capOnChow C f d

theorem capFun_picardClass (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L) :
    capFun C f d (Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf L hL) =
      (@invCap C X f _ L hL).capOnChow C f d := by
  let x := Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf L hL
  have h := Stacks.Picard.classOf_picardRepresentative X.toRingedSpace x
  obtain ⟨e⟩ := (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).mp h
  ext a
  exact @invCap_congr C X f _ (chosenLine x).1 L (chosenLine x).2 hL e d a

theorem capFun_add (x y : Stacks.Picard.ofScheme X) :
    capFun C f d (x + y) = capFun C f d x + capFun C f d y := by
  set Lx := Stacks.Picard.picardRepresentative X.toRingedSpace x
  set Ly := Stacks.Picard.picardRepresentative X.toRingedSpace y
  have hLxy := @Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ _ _ _ _ _ _
    Lx.property Ly.property
  have hsum : x + y = Stacks.SheafOfModules.picardClass X.presheaf X.ringCatIsSheaf
      (Scheme.Modules.tensorObj Lx.obj Ly.obj) hLxy := by
    conv_lhs => rw [← Stacks.Picard.classOf_picardRepresentative X.toRingedSpace x,
      ← Stacks.Picard.classOf_picardRepresentative X.toRingedSpace y]
    exact Stacks.SheafOfModules.picardClass_tensorSheaf _ _ _ _ _ _ hLxy
  rw [hsum, capFun_picardClass]
  apply AddMonoidHom.ext
  intro a
  have hLx : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property Lx.obj :=
    Lx.property
  have hLy : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property Ly.obj :=
    Ly.property
  have hLt : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Scheme.Modules.tensorObj Lx.obj Ly.obj) := hLxy
  change (invCap C f (Scheme.Modules.tensorObj Lx.obj Ly.obj)).capOnChow C f d a =
    (invCap C f Lx.obj).capOnChow C f d a + (invCap C f Ly.obj).capOnChow C f d a
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective _ a
  rw [invCap_capOnChow_mk, invCap_capOnChow_mk, invCap_capOnChow_mk]
  exact (firstChernClassCapOfInvertible_tensorObj C f d Lx.obj Ly.obj b).symm

def capHom : Stacks.Picard.ofScheme X →+
    (chowGroup C f (d + 1) →+ chowGroup C f d) :=
  AddMonoidHom.mk' (capFun C f d) (capFun_add C f d)

theorem capHom_apply (x : Stacks.Picard.ofScheme X) : capHom C f d x = capFun C f d x := rfl

theorem capFun_zero : capFun C f d 0 = 0 := (capHom C f d).map_zero

end M9Native.ChowPicardCap
