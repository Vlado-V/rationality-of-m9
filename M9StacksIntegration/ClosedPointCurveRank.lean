module

public import M9StacksIntegration.ClosedPointConstantRank
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

@[expose] public section

/-! Closed-point rank propagation on the actual smooth integral curve.

The finite type curve supplies Jacobson density, and smoothness supplies local
Noetherianity. The actual curve is integral and hence reduced. Over an
algebraically closed base, the base-point adapter uses the native closed-point
map and its actual residue-field isomorphism; it does not identify residue
fields definitionally with the base field.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.ClosedPointCurveRank

variable {X : Scheme.{u}}

/-- The actual finite type curve is a Jacobson scheme. -/
theorem jacobsonSpace_of_curve (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsCurve k f] : JacobsonSpace X :=
  LocallyOfFiniteType.jacobsonSpace f

/-- Closed-point ranks propagate to the actual residue fibres at all points
of the original smooth curve. -/
theorem everywhereRank_of_closedRank (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
    {F G : X.Modules} (φ : F ⟶ G) (m n r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F m)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n)
    (hclosed : ∀ x : X, IsClosed ({x} : Set X) →
      MukaiSemiIrreducible.mapRankAt φ x = r) :
    MukaiSemiIrreducible.EverywhereRank φ r := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular (isRegular_of_smooth_over_field f)
  let : JacobsonSpace X := jacobsonSpace_of_curve k f
  exact ClosedPointConstantRank.everywhereRank_of_closedRank φ m n r hF hG hclosed

/-- The original kernel, image, and cokernel are finite locally free of the
correct ranks, derived solely from the original ranks at closed points. -/
theorem ranks_of_closedRank (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
    {F G : X.Modules} (φ : F ⟶ G) (m n r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F m)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n)
    (hclosed : ∀ x : X, IsClosed ({x} : Set X) →
      MukaiSemiIrreducible.mapRankAt φ x = r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel φ) (m-r) ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (image φ) r ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (cokernel φ) (n-r) :=
  CurveConstantRank.ranks_on_smooth_curve k f φ m n r hF hG
    (everywhereRank_of_closedRank k f φ m n r hF hG hclosed)

/-- Canonical residue-fibre comparison for the actual original kernel. -/
def residueKernelEquiv_of_closedRank (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
    {F G : X.Modules} (φ : F ⟶ G) (m n r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F m)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n)
    (hclosed : ∀ x : X, IsClosed ({x} : Set X) →
      MukaiSemiIrreducible.mapRankAt φ x = r) (x : X) :
    TupleEvaluationFiber.Fiber (kernel φ) x ≃ₗ[X.residueField x]
      LinearMap.ker (TupleEvaluationFiber.inducedFiberMap φ x) :=
  CurveConstantRank.residueKernelEquiv_on_smooth_curve k f φ m n r hF hG
    (everywhereRank_of_closedRank k f φ m n r hF hG hclosed) x

/-- The derived comparison retains the literal original kernel inclusion. -/
theorem residueKernelEquiv_of_closedRank_ι (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
    {F G : X.Modules} (φ : F ⟶ G) (m n r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F m)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n)
    (hclosed : ∀ x : X, IsClosed ({x} : Set X) →
      MukaiSemiIrreducible.mapRankAt φ x = r) (x : X)
    (v : TupleEvaluationFiber.Fiber (kernel φ) x) :
    (residueKernelEquiv_of_closedRank k f φ m n r hF hG hclosed x v).val =
      TupleEvaluationFiber.inducedFiberMap (kernel.ι φ) x v := rfl

/-- Actual base-field points cover the closed points. The rank mentioned here
is the actual residue-map rank at the image point, without a definitional
identification of that residue field with the base field. -/
theorem closedRank_of_base_points (k : Type u) [Field k] [IsAlgClosed k]
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    {F G : X.Modules} (φ : F ⟶ G) (r : ℕ)
    (hp : ∀ p : Spec (.of k) ⟶ X, p ≫ f = 𝟙 _ →
      MukaiSemiIrreducible.mapRankAt φ (p (IsLocalRing.closedPoint k)) = r) :
    ∀ x : X, IsClosed ({x} : Set X) → MukaiSemiIrreducible.mapRankAt φ x = r := by
  intro x hx
  simpa using hp (pointOfClosedPoint f x hx) (pointOfClosedPoint_comp f x hx)

/-- Base-field point ranks, interpreted on the original residue fibres,
therefore suffice for all three locally free objects on the smooth curve. -/
theorem ranks_of_base_points (k : Type u) [Field k] [IsAlgClosed k]
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
    {F G : X.Modules} (φ : F ⟶ G) (m n r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F m)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n)
    (hp : ∀ p : Spec (.of k) ⟶ X, p ≫ f = 𝟙 _ →
      MukaiSemiIrreducible.mapRankAt φ (p (IsLocalRing.closedPoint k)) = r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel φ) (m-r) ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (image φ) r ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (cokernel φ) (n-r) :=
  ranks_of_closedRank k f φ m n r hF hG (closedRank_of_base_points k f φ r hp)

end M9Native.ClosedPointCurveRank
