module

public import M9StacksIntegration.CohenMacaulayCommonPointIntegral
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SerreCondition

/-! The actual Serre S1 version of the common-regular-point integrality
criterion, and genuine transport of Serre's predicates along a scheme iso. -/

set_option autoImplicit false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
namespace M9Native.SerreCommonPointIntegral

theorem hasPropertySk_of_iso {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (e : X ≅ Y) (k : ℕ) (h : HasPropertySk X k) :
    HasPropertySk Y k := by
  intro y
  let eR := (asIso (e.inv.stalkMap y)).commRingCatIsoToRingEquiv
  change min (k : WithBot ℕ∞) (ringKrullDim (Y.presheaf.stalk y)) ≤
    (Module.depth (Y.presheaf.stalk y) (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      (Y.presheaf.stalk y) : WithBot ℕ∞)
  rw [← ringKrullDim_eq_of_ringEquiv eR, ← Module.depth_self_eq_of_ringEquiv eR]
  exact h (e.inv y)

/-- Only actual S1 is needed to remove nilpotents after the actual common
regular point has forced irreducibility and generic regularity. -/
theorem integral_of_s1_of_components_common_regular_point
    (X : Scheme.{u}) [IsLocallyNoetherian X] (hS : HasPropertySk X 1)
    (x : X) (hx : IsRegularLocalRing (X.presheaf.stalk x))
    (hcomp : ∀ Z ∈ irreducibleComponents X, x ∈ Z) : IsIntegral X := by
  let : IsRegularLocalRing (X.presheaf.stalk x) := hx
  let : IsDomain (X.presheaf.stalk x) := IsRegularLocalRing.isDomain _
  let : IrreducibleSpace X :=
    CurveContainingComponents.irreducibleSpace_of_domain_stalk_of_components X x hcomp
  let : IsReduced X :=
    (isReduced_iff_hasPropertyS1_and_isRegularInCodimension_zero X).mpr
      ⟨hS, CohenMacaulayCommonPointIntegral.regularInCodimensionZero_of_regular_stalk X x hx⟩
  exact isIntegral_of_irreducibleSpace_of_isReduced X

end M9Native.SerreCommonPointIntegral
