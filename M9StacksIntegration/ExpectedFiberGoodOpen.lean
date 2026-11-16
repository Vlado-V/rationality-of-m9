module

public import M9StacksIntegration.ExpectedFiberSmoothness
public import M9StacksIntegration.ProperSmoothClosedPoints
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization

/-!
# A genuine expected smooth fibre lies in the canonical proper smooth open

Absolute smooth relative dimensions determine the actual dimensions at
closed points.  Miracle flatness and the native smooth-fibre criterion
prove relative smoothness there; closed specialization then proves it on
the whole original fibre.  The desired relative smoothness or membership
in the good open is not a premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace M9Native.ExpectedFiberGoodOpen

/-- A smooth irreducible actual fibre of the expected dimension lies in
the original canonical good open of a proper family with smooth absolute
source and target. -/
theorem mem_goodOpen_of_smooth_fiber {K : Type u} [Field K]
    {X Y : Scheme.{u}} {n m r : ℕ}
    (pX : X ⟶ Spec (.of K)) (pY : Y ⟶ Spec (.of K))
    [SmoothOfRelativeDimension n pX] [SmoothOfRelativeDimension m pY]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] [IsProper f]
    (y : Y) (hy : IsClosed ({y} : Set Y))
    [Smooth (f.fiberToSpecResidueField y)] [IrreducibleSpace (f.fiber y)]
    (hF : topologicalKrullDim (f.fiber y) = (r : WithBot ℕ∞)) (hn : n = m + r) :
    y ∈ ProperSmoothLocus.goodOpen f := by
  let : Smooth pX := SmoothOfRelativeDimension.smooth n pX
  let : Smooth pY := SmoothOfRelativeDimension.smooth m pY
  apply ProperSmoothClosedPoints.mem_goodOpen_of_closed_points f y hy
  intro x hxy hx
  subst y
  exact ExpectedFiberSmoothness.mem_smoothLocus_of_closed_dimensions pX pY f x hx hy
    (topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field n pX x)
    (topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field m pY (f x)) hF hn

/-- For an actual field-valued section the required closedness is
proved, so the conclusion uses only genuine absolute and fibre geometry. -/
theorem section_mem_goodOpen_of_smooth_fiber {K : Type u} [Field K]
    {X Y : Scheme.{u}} {n m r : ℕ}
    (pX : X ⟶ Spec (.of K)) (pY : Y ⟶ Spec (.of K))
    [SmoothOfRelativeDimension n pX] [SmoothOfRelativeDimension m pY]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] [IsProper f]
    (p : Spec (.of K) ⟶ Y) (hp : p ≫ pY = 𝟙 _)
    [Smooth (f.fiberToSpecResidueField (p (IsLocalRing.closedPoint K)))]
    [IrreducibleSpace (f.fiber (p (IsLocalRing.closedPoint K)))]
    (hF : topologicalKrullDim (f.fiber (p (IsLocalRing.closedPoint K))) = (r : WithBot ℕ∞))
    (hn : n = m + r) :
    p (IsLocalRing.closedPoint K) ∈ ProperSmoothLocus.goodOpen f :=
  mem_goodOpen_of_smooth_fiber pX pY f _
    (ProperSmoothClosedPoints.section_point_isClosed pY p hp _) hF hn

/-- The whole original field-valued parameter morphism lands in the
actual good open, as required by the original family base-change API. -/
theorem section_lands_goodOpen_of_smooth_fiber {K : Type u} [Field K]
    {X Y : Scheme.{u}} {n m r : ℕ}
    (pX : X ⟶ Spec (.of K)) (pY : Y ⟶ Spec (.of K))
    [SmoothOfRelativeDimension n pX] [SmoothOfRelativeDimension m pY]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] [IsProper f]
    (p : Spec (.of K) ⟶ Y) (hp : p ≫ pY = 𝟙 _)
    [Smooth (f.fiberToSpecResidueField (p (IsLocalRing.closedPoint K)))]
    [IrreducibleSpace (f.fiber (p (IsLocalRing.closedPoint K)))]
    (hF : topologicalKrullDim (f.fiber (p (IsLocalRing.closedPoint K))) = (r : WithBot ℕ∞))
    (hn : n = m + r) :
    ∀ t : Spec (.of K), p t ∈ ProperSmoothLocus.goodOpen f := by
  intro t
  have h := section_mem_goodOpen_of_smooth_fiber pX pY f p hp hF hn
  simpa only [Subsingleton.elim t (IsLocalRing.closedPoint K)] using h

end M9Native.ExpectedFiberGoodOpen
