module

public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup

/-!
# The actual K-zero relation for a section with locally free cokernel

An actual monomorphism from the structure sheaf whose actual cokernel is
finite locally free gives the native Grothendieck relation. This leaf
does not assume a splitting or a Chern-class equality. Establishing the
locally free cokernel of a nowhere-zero section is a separate geometric
step.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.SectionKZero

/-- The structure sheaf, typed in the native abelian category. -/
abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  _root_.SheafOfModules.unit X.ringCatSheaf

/-- The defining native short exact sequence of an actual section
with locally free cokernel gives its actual K-zero class. -/
theorem classOf_eq_unit_add_cokernel {X : Scheme.{u}} (H : X.Modules)
    (s : unitModule X ⟶ H) [hs : Mono s]
    (hH : SheafOfModules.IsFiniteLocallyFree.{u, u, u} H)
    (hC : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (cokernel s)) :
    VectorBundleKZero.classOf X H =
      1 + VectorBundleKZero.classOf X (cokernel s) := by
  have h := @VectorBundleKZero.classOf_shortExact X _ _ _ s (cokernel.π s) hs inferInstance
    (cokernel.condition s) (isFiniteLocallyFree_unit X) hH hC
    (ShortComplex.exact_cokernel s)
  simpa only [VectorBundleKZero.classOf_unit] using h

/-- The same actual relation ordered for the line-Chern coefficient
formula. -/
theorem classOf_eq_cokernel_add_unit {X : Scheme.{u}} (H : X.Modules)
    (s : unitModule X ⟶ H) [Mono s]
    (hH : SheafOfModules.IsFiniteLocallyFree.{u, u, u} H)
    (hC : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (cokernel s)) :
    VectorBundleKZero.classOf X H =
      VectorBundleKZero.classOf X (cokernel s) + 1 := by
  rw [classOf_eq_unit_add_cokernel H s hH hC, add_comm]

end M9Native.SectionKZero
