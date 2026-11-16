module

public import M9StacksIntegration.MukaiGeneratedImageTwist
public import M9StacksIntegration.MukaiGeneratedImageSections
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionPairing

/-!
# The actual Cartier-divisor relation in a generated image

Every extra section of Q(D) has its I_D multiple in Q. The relation is
the true canonical pairing, so the generated quotient is a quotient of
the literal cokernel of I_D→O_X.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace M9Native.MukaiGeneratedCartierImage

@[instance_reducible] local instance modulesMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.sheafTensorMonoidal X.sheaf.obj X.ringCatSheaf.property

@[instance_reducible] local instance modulesSymmetric (X : Scheme.{u}) :
    SymmetricCategory X.Modules :=
  Stacks.SheafOfModules.sheafTensorSymmetric X.sheaf.obj X.ringCatSheaf.property

variable {X : Scheme.{u}} (D : X.IdealSheafData)
variable [Stacks.Divisors.IsEffectiveCartierDivisor D]
variable (Q : X.Modules)

local instance idealInvertible :
    Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property (Stacks.Divisors.negativeTwist' D) :=
  Stacks.Divisors.isTensorInvertible_negativeTwist D

/-- The actual canonical morphism Q→Q(D). -/
abbrev inclusion : Q ⟶ Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D) :=
  MukaiGeneratedImage.twistInclusion (Stacks.Divisors.canonicalSectionHom D)

/-- Contract an arbitrary actual extra section of Q(D) against I_D. -/
def contraction (a : MukaiBundle.structureModule X ⟶
    Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D)) :
    Stacks.Divisors.negativeTwist' D ⟶ Q :=
  MukaiGeneratedImage.contractTwistedSection
    (C := X.Modules)
    (show Scheme.Modules.tensorObj (Stacks.Divisors.invertibleSheaf' D)
        (Stacks.Divisors.negativeTwist' D) ≅ MukaiBundle.structureModule X from
      Stacks.SheafOfModules.Scheme.evaluationIso X (Stacks.Divisors.negativeTwist' D)) a

/-- The literal ideal relation used to descend the extra generator to O_D. -/
theorem ideal_relation (a : MukaiBundle.structureModule X ⟶
    Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D)) :
    Stacks.Divisors.idealSheafInclusion D ≫ a = contraction D Q a ≫ inclusion D Q := by
  exact (MukaiGeneratedImage.contractTwistedSection_inclusion
    (C := X.Modules)
    (show Scheme.Modules.tensorObj (Stacks.Divisors.invertibleSheaf' D)
        (Stacks.Divisors.negativeTwist' D) ≅ MukaiBundle.structureModule X from
      Stacks.SheafOfModules.Scheme.evaluationIso X (Stacks.Divisors.negativeTwist' D))
    (Stacks.Divisors.idealSheafInclusion D) (Stacks.Divisors.canonicalSectionHom D)
    (Stacks.Divisors.tensorLeftMap_idealSheafInclusion_comp_tensorRightUnitor D) a).symm

/-- The generated image modulo Q is a genuine quotient of O_D, in its
literal cokernel presentation. -/
def divisorQuotientMap (a : MukaiBundle.structureModule X ⟶
    Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D)) :
    cokernel (Stacks.Divisors.idealSheafInclusion D) ⟶
      MukaiGeneratedImage.quotient (inclusion D Q) a :=
  MukaiGeneratedImage.quotientFromCokernel (inclusion D Q) a
    (Stacks.Divisors.idealSheafInclusion D) (contraction D Q a) (ideal_relation D Q a)

instance divisorQuotientMap_epi (a : MukaiBundle.structureModule X ⟶
    Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D)) :
    Epi (divisorQuotientMap D Q a) := by
  dsimp only [divisorQuotientMap]
  infer_instance

end M9Native.MukaiGeneratedCartierImage

