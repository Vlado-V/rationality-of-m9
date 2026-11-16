module

public import M9StacksIntegration.MukaiBundleTensor
public import M9StacksIntegration.ExteriorTensorLine
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorInvertibleSheaf

/-!
# The actual line cancellations in the tensor of Mukai's pencil sequence

The coefficient is beta tensor I_D tensor I_D, the bundle is Q(D), and
the quotient is the literal (I_D tensor beta) tensor Q. The constructed
isomorphisms cancel actual Cartier factors and identify the coefficient
times the actual determinant with the original residual canonical line.
No rank-two self-duality or cohomology identity is assumed here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory
open M9Native.MukaiBundle M9Native.MukaiBundleDeterminant
open M9Native.MukaiCupAlternating (exteriorSquare)

universe u

namespace M9Native.MukaiTensorLineCancellation

variable {X : Scheme.{u}}

abbrev tensorAssoc (A B C : X.Modules) : tensor (tensor A B) C ≅ tensor A (tensor B C) :=
  Stacks.SheafOfModules.Invertible.tensorProductAssociator X.presheaf X.ringCatSheaf.property A B C

abbrev tensorSwap (A B : X.Modules) : tensor A B ≅ tensor B A :=
  Stacks.SheafOfModules.Invertible.tensorProductBraiding X.presheaf X.ringCatSheaf.property A B

abbrev unitLeft (A : X.Modules) : tensor (structureModule X) A ≅ A :=
  Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor X.presheaf X.ringCatSheaf.property A

abbrev unitRight (A : X.Modules) : tensor A (structureModule X) ≅ A :=
  Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.presheaf X.ringCatSheaf.property A

/-- The actual interchange of the middle two tensor factors. -/
def middleFourIso (A B C E : X.Modules) :
    tensor (tensor A B) (tensor C E) ≅ tensor (tensor A C) (tensor B E) :=
  tensorAssoc A B (tensor C E) ≪≫
    tensorIso (Iso.refl A) (tensorAssoc B C E).symm ≪≫
    tensorIso (Iso.refl A) (tensorIso (tensorSwap B C) (Iso.refl E)) ≪≫
    tensorIso (Iso.refl A) (tensorAssoc C B E) ≪≫
    (tensorAssoc A C (tensor B E)).symm

variable (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]

abbrev ideal : X.Modules := Stacks.Divisors.negativeTwist' D
abbrev divisorLine : X.Modules := Stacks.Divisors.invertibleSheaf' D

local instance idealInvertible :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property (ideal D) :=
  Stacks.Divisors.isTensorInvertible_negativeTwist D

/-- The original Cartier evaluation pairing, with the ideal on the left. -/
def idealPairing : tensor (ideal D) (divisorLine D) ≅ structureModule X :=
  tensorSwap (ideal D) (divisorLine D) ≪≫
    (show tensor (divisorLine D) (ideal D) ≅ structureModule X from
      Stacks.SheafOfModules.Scheme.evaluationIso X (ideal D))

def idealTwoLineCancel : tensor (ideal D) (tensor (divisorLine D) (divisorLine D)) ≅
    divisorLine D :=
  (tensorAssoc (ideal D) (divisorLine D) (divisorLine D)).symm ≪≫
    tensorIso (idealPairing D) (Iso.refl (divisorLine D)) ≪≫ unitLeft (divisorLine D)

/-- The actual beta(-2D), with both original ideal factors retained. -/
abbrev coefficient (beta : X.Modules) : X.Modules := tensor beta (tensor (ideal D) (ideal D))

abbrev twist (Q : X.Modules) : X.Modules := tensor Q (divisorLine D)

/-- The literal right endpoint after tensoring the original pencil sequence by Q. -/
abbrev rightEndpoint (Q beta : X.Modules) : X.Modules := tensor (tensor (ideal D) beta) Q

/-- Cancel one original ideal factor against O(D), retaining the actual quotient. -/
def coefficientTwistIso (Q beta : X.Modules) :
    tensor (coefficient D beta) (twist D Q) ≅ rightEndpoint D Q beta :=
  tensorIso (tensorAssoc beta (ideal D) (ideal D)).symm (Iso.refl (twist D Q)) ≪≫
    middleFourIso (tensor beta (ideal D)) (ideal D) Q (divisorLine D) ≪≫
    tensorIso (Iso.refl (tensor (tensor beta (ideal D)) Q)) (idealPairing D) ≪≫
    unitRight (tensor (tensor beta (ideal D)) Q) ≪≫
    tensorIso (tensorSwap beta (ideal D)) (Iso.refl Q)

/-- Both original ideal factors cancel the two determinant twist factors. -/
def coefficientDeterminantIso (Q alpha beta Omega : X.Modules)
    (hdet : exteriorSquare Q ≅ alpha) (hres : tensor alpha beta ≅ Omega) :
    tensor (coefficient D beta) (exteriorSquare (twist D Q)) ≅ Omega := by
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property (divisorLine D) :=
    Stacks.Divisors.invertibleSheaf_isInvertible D
  exact
    tensorIso (tensorAssoc beta (ideal D) (ideal D)).symm
      (M9Native.ExteriorTensorLine.exteriorTensorLineIso Q (divisorLine D)) ≪≫
    middleFourIso (tensor beta (ideal D)) (ideal D) (exteriorSquare Q)
      (tensor (divisorLine D) (divisorLine D)) ≪≫
    tensorIso (Iso.refl (tensor (tensor beta (ideal D)) (exteriorSquare Q)))
      (idealTwoLineCancel D) ≪≫
    tensorAssoc (tensor beta (ideal D)) (exteriorSquare Q) (divisorLine D) ≪≫
    middleFourIso beta (ideal D) (exteriorSquare Q) (divisorLine D) ≪≫
    tensorIso (Iso.refl (tensor beta (exteriorSquare Q))) (idealPairing D) ≪≫
    unitRight (tensor beta (exteriorSquare Q)) ≪≫
    tensorSwap beta (exteriorSquare Q) ≪≫ tensorIso hdet (Iso.refl beta) ≪≫ hres

end M9Native.MukaiTensorLineCancellation
