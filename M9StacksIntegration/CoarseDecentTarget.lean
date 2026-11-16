module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.LocallySeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

@[expose] public section

/-! Decency of the original separated algebraic-space target.  This is
derived from its genuine relative diagonal, and is not supplied as an
additional premise in the actual coarse-space application. -/

open AlgebraicGeometry

namespace M9Native.CoarseDecentTarget

universe u

/-- An actual separated algebraic space is decent, over its original base. -/
theorem decent_of_separated (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Y : AlgebraicSpaces B S hS) (hs : Space.IsSeparatedOver B S hS Y.obj) :
    Space.IsDecentSpace B S hS Y.obj :=
  Space.isDecentSpace_of_isLocallySeparatedOver B S hS Y.property
    (Space.isImmersion_of_isClosedImmersion B S hS hs)

end M9Native.CoarseDecentTarget
