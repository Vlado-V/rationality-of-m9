module

public import M9StacksIntegration.Sp6AffineBaseChange

/-! Uniqueness of the actual integer-base scalar structure. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory

namespace M9Native.Sp6IntegerAlgebraCoherence

open Sp6AffineBaseChange (IntegerRing tensorObject)

theorem integerAlgebra_eq (A : Type u) [CommRing A]
    (P Q : Algebra IntegerRing.{u} A) : P = Q := by
  apply Algebra.algebra_ext P Q
  intro x
  have h : P.algebraMap.comp ULift.ringEquiv.symm.toRingHom =
      Q.algebraMap.comp ULift.ringEquiv.symm.toRingHom :=
    Subsingleton.elim _ _
  exact congrArg (fun f : ℤ →+* A => f x.down) h

theorem tensorObject_eq (S T : Type u) [CommRing S] [CommRing T]
    (a b : Algebra IntegerRing.{u} S) (p q : Algebra IntegerRing.{u} T) :
    @tensorObject IntegerRing.{u} S T inferInstance inferInstance inferInstance a p =
      @tensorObject IntegerRing.{u} S T inferInstance inferInstance inferInstance b q := by
  exact congrArg₂ (fun α β =>
    @tensorObject IntegerRing.{u} S T inferInstance inferInstance inferInstance α β)
    (integerAlgebra_eq S a b) (integerAlgebra_eq T p q)

def tensorOver (S T : Type u) [CommRing S] [CommRing T]
    (a : Algebra IntegerRing.{u} S) (p : Algebra IntegerRing.{u} T) :
    Over (Spec (.of S)) := by
  letI := a
  letI := p
  letI := Sp6AffineBaseChange.tensorObjectLeftAlgebra IntegerRing S T
  exact Over.mk (Sp6AffineBaseChange.specAlgebraMap S (tensorObject IntegerRing S T))

theorem tensorOver_eq (S T : Type u) [CommRing S] [CommRing T]
    (a b : Algebra IntegerRing.{u} S) (p q : Algebra IntegerRing.{u} T) :
    tensorOver S T a p = tensorOver S T b q :=
  congrArg₂ (tensorOver S T) (integerAlgebra_eq S a b) (integerAlgebra_eq T p q)

end M9Native.Sp6IntegerAlgebraCoherence
