module

public import M9StacksIntegration.MukaiGeneratedCartierImage
public import M9StacksIntegration.MukaiGeneratedQuotient
public import M9StacksIntegration.CurveDivisorSections

/-!
# Untwisting an actual quotient of Q(D)

The original quotient morphism is tensor-cancelled using the actual
Cartier evaluation isomorphism. The resulting quotient of Q has two
sections when Q is generated and has no map to the structure sheaf.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open M9StacksIntegration.InvertibleHomCancellation (tensorRight)

universe u

namespace M9Native.MukaiTwistedQuotient

@[instance_reducible] local instance modulesMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.sheafTensorMonoidal X.sheaf.obj X.ringCatSheaf.property

@[instance_reducible] local instance modulesSymmetric (X : Scheme.{u}) :
    SymmetricCategory X.Modules :=
  Stacks.SheafOfModules.sheafTensorSymmetric X.sheaf.obj X.ringCatSheaf.property

variable {X : Scheme.{u}} (D : X.IdealSheafData)
variable [Stacks.Divisors.IsEffectiveCartierDivisor D]

local instance idealInvertible :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (Stacks.Divisors.negativeTwist' D) :=
  Stacks.Divisors.isTensorInvertible_negativeTwist D

/-- Actual cancellation of the positive and negative Cartier factors. -/
def untwistIso (Q : X.Modules) :
    (tensorRight (Stacks.Divisors.negativeTwist' D)).obj
      (Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D)) ≅ Q :=
  (α_ Q (Stacks.Divisors.invertibleSheaf' D) (Stacks.Divisors.negativeTwist' D)) ≪≫
    whiskerLeftIso Q (show
      Scheme.Modules.tensorObj (Stacks.Divisors.invertibleSheaf' D)
        (Stacks.Divisors.negativeTwist' D) ≅ MukaiBundle.structureModule X from
      Stacks.SheafOfModules.Scheme.evaluationIso X (Stacks.Divisors.negativeTwist' D)) ≪≫
    (ρ_ Q)

/-- The genuine quotient map Q → N(-D), obtained from Q(D) → N. -/
def untwistQuotient (Q N : X.Modules)
    (q : Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D) ⟶ N) :
    Q ⟶ (tensorRight (Stacks.Divisors.negativeTwist' D)).obj N :=
  (untwistIso D Q).inv ≫ (tensorRight (Stacks.Divisors.negativeTwist' D)).map q

instance untwistQuotient_epi (Q N : X.Modules)
    (q : Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D) ⟶ N) [Epi q] :
    Epi (untwistQuotient D Q N q) := by
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (Stacks.Divisors.negativeTwist' D) := Stacks.Divisors.isInvertible_negativeTwist D
  letI : (tensorRight (Stacks.Divisors.negativeTwist' D)).IsEquivalence :=
    Scheme.Modules.isEquivalence_invertibleTensorRightFunctor _
  dsimp only [untwistQuotient]
  infer_instance

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
variable [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]

/-- The untwisted quotient has at least two actual sections. -/
theorem two_le_h0_untwist (Q N : X.Modules)
    [hN : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N]
    [Module.Finite k (cohomologyOverField k f
      ((tensorRight (Stacks.Divisors.negativeTwist' D)).obj N) 0)]
    (q : Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D) ⟶ N) [Epi q]
    (hgen : MukaiSemiIrreducible.GloballyGenerated Q)
    (hvan : ∀ v : Q ⟶ MukaiBundle.structureModule X, v = 0) :
    2 ≤ Module.finrank k (cohomologyOverField k f
      ((tensorRight (Stacks.Divisors.negativeTwist' D)).obj N) 0) := by
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (Stacks.Divisors.negativeTwist' D) := Stacks.Divisors.isInvertible_negativeTwist D
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      ((tensorRight (Stacks.Divisors.negativeTwist' D)).obj N) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf
      X.ringCatSheaf.property N (Stacks.Divisors.negativeTwist' D)
  exact MukaiGeneratedQuotient.two_le_h0_of_generated_no_unit_hom f Q _ hgen
    (untwistQuotient D Q N q) hvan

end M9Native.MukaiTwistedQuotient
