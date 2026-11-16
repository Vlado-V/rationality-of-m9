module

public import M9StacksIntegration.SymmetricSquareIntegerTensorPower
public import StacksFrontier.AlgebraicGeometry.Ample.AmpleCriteria
public import StacksFrontier.AlgebraicGeometry.Modules.ExteriorPowerDeterminant

/-!
# Actual short-exact-sequence adjunction and native integer line powers

This is the reusable determinant calculation for the genuine five-section
conormal sequence. The sequence, endpoint ranks and determinant identifications
are explicit mathematical inputs. The quotient-line isomorphism is constructed
from the original short exact sequence and native integer-power cancellation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open M9Native.MukaiBundleDeterminant
open M9Native.SymmetricSquareIntegerTensorPower

universe u

namespace M9Native.LagrangianCurveAdjunction

variable {X : Scheme.{u}}

/-- Invertibility of the actual native integer power, derived from that of the original line. -/
theorem integerPower_isInvertible (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (a : ℤ) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L a) :=
  Stacks.SheafOfModules.Invertible.tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 L a

/-- Cancellation uses the actual tensor functor's proved equivalence. -/
def cancelIntegerLeft (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (a : ℤ)
    {P Q : X.Modules}
    (e : tensor (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L a) P ≅
      tensor (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L a) Q) :
    P ≅ Q := by
  let A := Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L a
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A :=
    integerPower_isInvertible L a
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj A
  letI : T.IsEquivalence :=
    Stacks.SheafOfModules.tensorLeftFunctor_isEquivalence X.presheaf X.ringCatSheaf.2 A
  exact T.preimageIso e

/-- A true successive-power tensor relation determines the original quotient line. -/
def quotientIsoOfSuccessivePowers (L Q : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (a : ℤ)
    (e : tensor (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L a) Q ≅
      Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (a + 1)) :
    Q ≅ L := by
  let j : tensor (Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L a) L ≅
      Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (a + 1) :=
    tensorIso (Iso.refl _)
      (Stacks.SheafOfModules.Invertible.tensorPowerOneIso X.presheaf X.ringCatSheaf.2 L).symm ≪≫
        integerMultiplication L a 1
  exact cancelIntegerLeft L a (e ≪≫ j.symm)

/-- The actual middle rank follows from the original exact sequence and endpoint ranks. -/
theorem middle_rank (S : ShortComplex X.Modules) (hS : S.ShortExact) (r : ℕ)
    [h₁ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₁ r]
    [h₃ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₃ 1] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₂ (r + 1) :=
  MukaiBundle.extension_rank S hS r 1 h₁ h₃

/-- The genuine top-exterior isomorphism of the original short exact sequence
and successive native line powers construct the actual quotient-line isomorphism. -/
def quotientIsoOfDeterminants (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (r : ℕ) (L : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₁ r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₃ 1]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (a : ℤ)
    (d₁ : topExterior S.X₁ r ≅
      Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L a)
    (d₂ : topExterior S.X₂ (r + 1) ≅
      Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (a + 1)) :
    S.X₃ ≅ L := by
  let eS : tensor (topExterior S.X₁ r) S.X₃ ≅ topExterior S.X₂ (r + 1) :=
    tensorIso (Iso.refl _) (Scheme.Modules.exteriorPowerOneIsoSelf S.X₃).symm ≪≫
      Scheme.Modules.exteriorPowerTensorExteriorPowerIso S.f S.g S.zero hS r 0
  exact quotientIsoOfSuccessivePowers L S.X₃ a
    (tensorIso d₁.symm (Iso.refl _) ≪≫ eS ≪≫ d₂)

/-- The five-section adjunction calculation: the genuine conormal determinant
has exponent -5 and the genuine restricted ambient determinant exponent -4. -/
def fiveSectionAdjunction (S : ShortComplex X.Modules) (hS : S.ShortExact) (L : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₁ 5]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₃ 1]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (d₁ : topExterior S.X₁ 5 ≅
      Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (-5))
    (d₂ : topExterior S.X₂ 6 ≅
      Stacks.SheafOfModules.Invertible.tensorPower X.presheaf X.ringCatSheaf.2 L (-4)) :
    S.X₃ ≅ L :=
  quotientIsoOfDeterminants S hS 5 L (-5) d₁ d₂

end M9Native.LagrangianCurveAdjunction
