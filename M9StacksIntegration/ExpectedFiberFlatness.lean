module

public import StacksFrontier.RingTheory.Flat.MiracleFlatness
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk

/-!
# Actual stalk flatness from the expected smooth-fibre dimension

This is native miracle flatness applied to the original map of local
rings.  The fibre term is the actual scheme-theoretic fibre stalk, using
the native quotient-to-fibre equivalence.  Flatness is a conclusion.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.ExpectedFiberFlatness

/-- A map between regular local scheme stalks with the expected actual
fibre-stalk dimension is flat at that point. -/
theorem flat_stalkMap_of_dimension_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    [IsRegularLocalRing (Y.presheaf.stalk (f x))]
    [IsRegularLocalRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) =
      ringKrullDim (Y.presheaf.stalk (f x)) +
        ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x))) :
    (f.stalkMap x).hom.Flat := by
  let R := Y.presheaf.stalk (f x)
  let S := X.presheaf.stalk x
  letI : Algebra R S := (f.stalkMap x).hom.toAlgebra
  haveI : IsLocalHom (algebraMap R S) := inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have hq : ringKrullDim S = ringKrullDim R +
      ringKrullDim (S ⧸ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R)) :=
    hdim.trans (congrArg (fun d => ringKrullDim R + d)
      (ringKrullDim_eq_of_ringEquiv (quotientStalkEquivFiberStalk f x)).symm)
  exact RingHom.flat_algebraMap_iff.mpr
    (Module.Flat.of_isMaximalCohenMacaulay_of_ringKrullDim_eq_add
      (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay S).2 hq)

end M9Native.ExpectedFiberFlatness
