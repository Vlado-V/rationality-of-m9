module

public import M9StacksIntegration.PoincarePicardTensor
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.Evaluation
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree

/-!
# The actual dual line has the negative actual Picard class

The actual evaluation isomorphism `L∨ ⊗ L ≅ O` and the already proved
native Picard tensor/isomorphism formulas imply the negative-class
identity. This is an actual line-bundle statement, not a formal root
sign convention or a Chern-class assumption.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.DualLinePicard

theorem dual_isInvertible {X : Scheme.{u}} (L : X.Modules)
    (hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (dualSheaf L) := by
  let : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL
  exact (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1
    (Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf X.presheaf X.ringCatSheaf.2 L)

theorem lineClass_dual {X : Scheme.{u}} (L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    letI : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (dualSheaf L) :=
      Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf X.presheaf X.ringCatSheaf.2 L
    PoincareChern.lineClass (dualSheaf L) = -PoincareChern.lineClass L := by
  letI : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (dualSheaf L) :=
    Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf X.presheaf X.ringCatSheaf.2 L
  letI : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (SheafOfModules.unit X.ringCatSheaf) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      (AlgebraicGeometry.SheafOfModules.isInvertible_unit X.presheaf X.ringCatSheaf.2)
  letI : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Scheme.Modules.tensorObj (dualSheaf L) L) :=
    PoincareChern.lineTensor_isInvertible _ _
  let e : Scheme.Modules.tensorObj (dualSheaf L) L ≅
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) :=
    Stacks.SheafOfModules.Scheme.evaluationIso X L
  have h : PoincareChern.lineClass (dualSheaf L) + PoincareChern.lineClass L = 0 := by
    calc
      _ = PoincareChern.lineClass (Scheme.Modules.tensorObj (dualSheaf L) L) :=
        (PoincareChern.lineClass_tensor _ _).symm
      _ = PoincareChern.lineClass (show X.Modules from SheafOfModules.unit X.ringCatSheaf) :=
        PoincareChern.lineClass_congr e
      _ = 0 := Stacks.SheafOfModules.picardClass_zero X.presheaf X.ringCatIsSheaf
  exact eq_neg_iff_add_eq_zero.mpr h

end M9Native.DualLinePicard
