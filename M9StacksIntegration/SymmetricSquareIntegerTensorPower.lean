module

public import M9StacksIntegration.SymmetricSquareBundleDeterminant
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerBridge
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerMultiplication
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.InversePairing

/-!
# Actual positive powers of the dual and native negative integer powers

The negative power is the native integer iterate of the right-tensor
functor. Its comparison with powers of the actual dual is derived from
its genuine inverse pairing and the native multiplication maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundleDeterminant

universe u

namespace M9Native.SymmetricSquareIntegerTensorPower

variable {X : Scheme.{u}}

/-- Functoriality of the actual recursively formed positive tensor powers. -/
def positiveTensorCongr {A B : X.Modules} (e : A ≅ B) :
    (n : ℕ) → SheafOfModules.tensorPower (Opens.grothendieckTopology X) A n ≅
      SheafOfModules.tensorPower (Opens.grothendieckTopology X) B n
  | 0 => Iso.refl _
  | 1 => e
  | n + 2 => tensorIso e (positiveTensorCongr e (n + 1))

/-- The actual native negative first iterate is the actual sheaf dual. -/
def dualIsoNegativeOne (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    dualSheaf L ≅ Stacks.SheafOfModules.Invertible.tensorPower
      X.presheaf X.ringCatSheaf.2 L (-1) := by
  let N := Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (-1)
  let e : tensor L N ≅ SheafOfModules.unit X.ringCatSheaf :=
    tensorIso
      (Stacks.SheafOfModules.Invertible.tensorPowerOneIso X.presheaf X.ringCatSheaf.2 L).symm
      (Iso.refl N) ≪≫
    Stacks.SheafOfModules.Invertible.tensorPowerMulIsoNegOne X.presheaf X.ringCatSheaf.2 L
  exact (tensorInverseNativeIso L N e).symm

/-- The existing native integer multiplication, at the original scheme sheaves. -/
def integerMultiplication (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (a b : ℤ) :
    tensor
      (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L a)
      (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L b) ≅
        Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (a + b) := by
  letI := Stacks.SheafOfModules.isEquivalence_tensorRightFunctor_of_isInvertible
    X.presheaf X.ringCatSheaf.2 L
  exact Stacks.SheafOfModules.TensorPower.tensorPowerMulIso X.presheaf X.ringCatSheaf.2 L a b

/-- Every actual positive tensor power of the dual is the native negative integer power. -/
def positiveDualIsoNegative (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    (n : ℕ) → SheafOfModules.tensorPower (Opens.grothendieckTopology X) (dualSheaf L) n ≅
      Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (-(n : ℤ))
  | 0 => Iso.refl _
  | 1 => dualIsoNegativeOne L
  | n + 2 =>
      tensorIso (dualIsoNegativeOne L) (positiveDualIsoNegative L (n + 1)) ≪≫
        integerMultiplication L (-1) (-((n + 1 : ℕ) : ℤ)) ≪≫
        Stacks.SheafOfModules.Invertible.tensorPowerReindex X.presheaf X.ringCatSheaf.2 L
          (by push_cast; ring : (-1 : ℤ) + -((n + 1 : ℕ) : ℤ) = -((n + 2 : ℕ) : ℤ))

end M9Native.SymmetricSquareIntegerTensorPower
