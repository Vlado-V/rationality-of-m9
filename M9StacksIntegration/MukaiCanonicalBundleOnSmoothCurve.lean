module

public import M9StacksIntegration.MukaiCanonicalBundleFromNet
public import M9StacksIntegration.Private.CurveCanonicalInvertibility

/-!
# The canonical Mukai bundle on the original smooth curve

Smoothness supplies invertibility of the actual dualizing sheaf through
its native right-adjoint construction.  The existence input is only an
original degree-eight net.  The resulting rank-three bundle is unique
up to an actual isomorphism with its full complete-system properties.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.MukaiCanonicalBundleOnSmoothCurve

open MukaiCanonicalBundleFromNet

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]

/-- The actual smooth genus-nine curve and one actual degree-eight net
produce its unique canonical, generated, completely semi-irreducible bundle. -/
theorem exists_unique_up_to_iso_from_net
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (A : LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 8 2) :
    ∃ E : X.Modules, IsCanonicalGeneratedSemi f E ∧
      ∀ F : X.Modules, IsCanonicalGeneratedSemi f F → Nonempty (E ≅ F) := by
  let := CurveCanonicalInvertibility.dualizing_isInvertible f
  exact MukaiCanonicalBundleFromNet.exists_unique_up_to_iso_from_net f hg hnp A

/-- Brill--Noether existence is the sole net-existence input.  No canonical
invertibility, residual-net, basis, extension or bundle property is assumed. -/
theorem exists_unique_up_to_iso_of_net_exists
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (hnet : Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 8 2)) :
    ∃ E : X.Modules, IsCanonicalGeneratedSemi f E ∧
      ∀ F : X.Modules, IsCanonicalGeneratedSemi f F → Nonempty (E ≅ F) := by
  obtain ⟨A⟩ := hnet
  exact exists_unique_up_to_iso_from_net f hg hnp A

end M9Native.MukaiCanonicalBundleOnSmoothCurve
