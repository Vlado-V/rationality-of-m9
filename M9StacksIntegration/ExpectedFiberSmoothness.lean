module

public import M9StacksIntegration.ExpectedFiberClosedPoints
public import StacksFrontier.AlgebraicGeometry.Closure.Condition2
public import StacksFrontier.AlgebraicGeometry.SmoothAtJacobian.StalkCriterion

/-!
# Relative smoothness from actual expected fibre data

Native miracle flatness gives flatness of the original stalk map.  The
native flat-plus-smooth-fibre criterion then proves actual relative
smoothness, hence membership in the original smooth locus.  Relative
smoothness of the desired morphism is not an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace M9Native.ExpectedFiberSmoothness

/-- Native Tag 01V9 proves smoothness of the original morphism at the
point from flatness of its original stalk map and its actual smooth fibre. -/
theorem smoothAt_of_flat_of_smooth_fiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (x : X)
    (hflat : (f.stalkMap x).hom.Flat)
    [Smooth (f.fiberToSpecResidueField (f x))] :
    InfinitesimalLifting.SmoothAt f x :=
  Stacks.Tag01V9Closure.condition2_imp_condition1 f x
    ⟨hflat, InfinitesimalLifting.smoothAt_of_smooth (f.fiberToSpecResidueField (f x)) (f.asFiber x)⟩

/-- The resulting point belongs to the original actual smooth locus. -/
theorem mem_smoothLocus_of_flat_of_smooth_fiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (x : X)
    (hflat : (f.stalkMap x).hom.Flat)
    [Smooth (f.fiberToSpecResidueField (f x))] : x ∈ f.smoothLocus :=
  (Stacks.SmoothAtJacobian.condition1_iff_mem_smoothLocus f x).mp
    (smoothAt_of_flat_of_smooth_fiber f x hflat)

/-- Regular original stalks and the actual expected fibre-stalk dimension
suffice: flatness and relative smoothness are both derived. -/
theorem mem_smoothLocus_of_regular_dimensions {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (x : X)
    [IsRegularLocalRing (Y.presheaf.stalk (f x))]
    [IsRegularLocalRing (X.presheaf.stalk x)]
    [Smooth (f.fiberToSpecResidueField (f x))]
    (hdim : ringKrullDim (X.presheaf.stalk x) =
      ringKrullDim (Y.presheaf.stalk (f x)) +
        ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x))) :
    x ∈ f.smoothLocus :=
  mem_smoothLocus_of_flat_of_smooth_fiber f x
    (ExpectedFiberFlatness.flat_stalkMap_of_dimension_eq f x hdim)

/-- The closed-point geometric adapter derives actual relative smoothness
from absolute smoothness and the actual expected fibre dimension. -/
theorem mem_smoothLocus_of_closed_dimensions {K : Type u} [Field K]
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of K)) (pY : Y ⟶ Spec (.of K))
    [Smooth pX] [Smooth pY] (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (x : X) (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({f x} : Set Y))
    [Smooth (f.fiberToSpecResidueField (f x))] [IrreducibleSpace (f.fiber (f x))]
    {n m r : ℕ} (hX : topologicalKrullDimAt X x = (n : WithBot ℕ∞))
    (hY : topologicalKrullDimAt Y (f x) = (m : WithBot ℕ∞))
    (hF : topologicalKrullDim (f.fiber (f x)) = (r : WithBot ℕ∞)) (hn : n = m + r) :
    x ∈ f.smoothLocus :=
  mem_smoothLocus_of_flat_of_smooth_fiber f x
    (ExpectedFiberClosedPoints.flat_stalkMap_of_closed_dimensions pX pY f x hx hy hX hY hF hn)

end M9Native.ExpectedFiberSmoothness
