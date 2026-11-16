module

public import M9StacksIntegration.SectionCokernelLocallyFree
public import M9StacksIntegration.SectionKZero
public import M9StacksIntegration.ZeroSchemeBaseFieldPoints

/-!
# Actual base-field nonvanishing gives an actual locally free cokernel

Over an algebraically closed field, the actual zero-ideal universal
property and closed-point theorem turn base-field nonvanishing of a
section into genuine nonzero field fibers of its actual unit morphism.
The genuine duality/Nakayama theorem then supplies the actual
monomorphism and the actual cokernel's rank. The resulting actual
K-zero relation is derived from the native short exact sequence.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.BaseFieldSectionCokernel

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  (q : X ⟶ Spec (.of K)) [LocallyOfFiniteType q]
  (H : X.Modules) (r : ℕ)
  [hH : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} H r]
  (s : SectionKZero.unitModule X ⟶ H)
  (hs : ∀ (p : Spec (.of K) ⟶ X), p ≫ q = 𝟙 _ →
    pullbackGlobalSections p H (UnitSectionPullback.unitSection s) ≠ 0)

include q r hs

/-- Nonvanishing over the base field suffices for genuine field-fiber
nonvanishing of the actual structure-sheaf morphism. -/
theorem nonzeroFieldFibers : SectionCokernelLocallyFree.NonzeroFieldFibers s := by
  intro L _ p
  apply SectionPullbackNonvanishing.pullback_map_ne_zero_of_unitSection_ne_zero p s
  exact ZeroSchemeBaseFieldPoints.field_pullback_ne_zero_of_base_field_pullbacks_ne_zero
    q H r (UnitSectionPullback.unitSection s) hs L p

theorem mono : Mono s :=
  SectionCokernelLocallyFree.mono_of_nonzeroFieldFibers s r hH
    (nonzeroFieldFibers q H r s hs)

/-- The actual categorical cokernel is genuinely finite locally free
of rank one less. No quotient flatness or local splitting is a premise. -/
theorem cokernel_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (cokernel s) (r-1) :=
  SectionCokernelLocallyFree.cokernel_rank s r hH
    (nonzeroFieldFibers q H r s hs)

/-- The actual unit-section cokernel gives the actual K-zero relation
from base-field nonvanishing alone. -/
theorem classOf_eq_cokernel_add_unit :
    VectorBundleKZero.classOf X H = VectorBundleKZero.classOf X (cokernel s) + 1 := by
  let := mono q H r s hs
  exact SectionKZero.classOf_eq_cokernel_add_unit H s hH.isFiniteLocallyFree
    (cokernel_rank q H r s hs).isFiniteLocallyFree

end M9Native.BaseFieldSectionCokernel
