module

public import M9StacksIntegration.MukaiPencilQuotient
public import M9StacksIntegration.MukaiCupAlternating
public import M9StacksIntegration.MukaiTensorLineCancellation

/-!
# The literal tensor of Mukai's constructed pencil sequence

The original maps of the original complete dual span are tensored by Q.
Exactness follows from finite local freeness, and the three displayed
endpoint isomorphisms retain the original cohomology and tensor bundles.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open M9Native.MukaiBundle M9Native.MukaiBundleDeterminant
open M9Native.MukaiDualSpanSections M9Native.CurveDivisorSections

universe u

namespace M9Native.MukaiTensorPencilSequence

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
variable (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
variable (beta : X.Modules)
variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property beta]
variable (bP : Module.Basis (ULift.{u} (Fin 2)) k (cohomologyOverField k f (twistDown D beta) 0))
variable (bB : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f beta 0))
variable (hP : Epi (MukaiPencilQuotient.pencilEvaluation (twistDown D beta)
  (MukaiPencilQuotient.completePencilSections f D beta bP)))
variable (hB : Epi (netEvaluation beta (completeNetSections f beta bB)))

local instance tensorAdditive (Q : X.Modules) : (MukaiCupAlternating.tensorRight Q).Additive :=
  MukaiCupAlternating.tensorRight_additive Q

/-- These are the actual original maps under the actual tensor functor. -/
def tensorSequence (Q : X.Modules) : ShortComplex X.Modules :=
  (MukaiPencilQuotient.completePencilSequence f D beta bP bB hP hB).map
    (MukaiCupAlternating.tensorRight Q)

theorem tensorSequence_shortExact (Q : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u,u,u} Q] :
    (tensorSequence f D beta bP bB hP hB Q).ShortExact := by
  letI : PreservesFiniteLimits (MukaiCupAlternating.tensorRight Q) :=
    (MukaiCupAlternating.tensorRight_exact Q inferInstance).1
  letI : PreservesFiniteColimits (MukaiCupAlternating.tensorRight Q) :=
    (MukaiCupAlternating.tensorRight_exact Q inferInstance).2
  exact (MukaiPencilQuotient.completePencilSequence_shortExact f D beta bP bB hP hB).map_of_exact
    (MukaiCupAlternating.tensorRight Q)

def leftEndpointIso (Q : X.Modules) :
    (tensorSequence f D beta bP bB hP hB Q).X₁ ≅ MukaiTensorLineCancellation.twist D Q :=
  MukaiTensorLineCancellation.tensorSwap (Stacks.Divisors.divisorSheaf D) Q

def middleEndpointIso (Q : X.Modules) :
    (tensorSequence f D beta bP bB hP hB Q).X₂ ≅
      tensor Q (dualSpan beta (completeNetSections f beta bB)) :=
  MukaiTensorLineCancellation.tensorSwap (dualSpan beta (completeNetSections f beta bB)) Q

def rightEndpointIso (Q : X.Modules) :
    (tensorSequence f D beta bP bB hP hB Q).X₃ ≅
      MukaiTensorLineCancellation.rightEndpoint D Q beta := Iso.refl _

end M9Native.MukaiTensorPencilSequence
