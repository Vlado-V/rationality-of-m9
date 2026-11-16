module

public import M9StacksIntegration.RationalSectionFiber
public import M9StacksIntegration.ExpectedFiberGoodOpen

/-! The expected smooth rational-point curve lies in the actual canonical
proper smooth open.  The actual pullback curve is compared with the actual
residue-field fibre by the proved rational-section isomorphism. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.RationalSectionGoodOpen

/-- Original absolute smooth dimensions and the original smooth integral
rational-point pullback prove membership in the actual good open. -/
theorem section_mem_goodOpen_of_smooth_pullback {K : Type u} [Field K]
    {X Y : Scheme.{u}} {n m r : ℕ}
    (pX : X ⟶ Spec (.of K)) (pY : Y ⟶ Spec (.of K))
    [SmoothOfRelativeDimension n pX] [SmoothOfRelativeDimension m pY]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] [IsProper f]
    (p : Spec (.of K) ⟶ Y) (hp : p ≫ pY = 𝟙 _)
    [Smooth (pullback.snd f p)] [IrreducibleSpace (pullback (C := Scheme.{u}) f p)]
    (hF : topologicalKrullDim (pullback (C := Scheme.{u}) f p) = (r : WithBot ℕ∞))
    (hn : n = m + r) :
    p (IsLocalRing.closedPoint K) ∈ ProperSmoothLocus.goodOpen f := by
  let : Smooth (f.fiberToSpecResidueField (p (IsLocalRing.closedPoint K))) :=
    RationalSectionFiber.fiber_smooth K pY f p hp
  let : IrreducibleSpace (f.fiber (p (IsLocalRing.closedPoint K))) :=
    RationalSectionFiber.fiber_irreducible K pY f p hp
  exact ExpectedFiberGoodOpen.section_mem_goodOpen_of_smooth_fiber pX pY f p hp
    (RationalSectionFiber.fiber_dimension K pY f p hp hF) hn

/-- Every point of the original rational parameter lies in the canonical
actual good open, with no relative-smoothness premise on the family. -/
theorem section_lands_goodOpen_of_smooth_pullback {K : Type u} [Field K]
    {X Y : Scheme.{u}} {n m r : ℕ}
    (pX : X ⟶ Spec (.of K)) (pY : Y ⟶ Spec (.of K))
    [SmoothOfRelativeDimension n pX] [SmoothOfRelativeDimension m pY]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f] [IsProper f]
    (p : Spec (.of K) ⟶ Y) (hp : p ≫ pY = 𝟙 _)
    [Smooth (pullback.snd f p)] [IrreducibleSpace (pullback (C := Scheme.{u}) f p)]
    (hF : topologicalKrullDim (pullback (C := Scheme.{u}) f p) = (r : WithBot ℕ∞))
    (hn : n = m + r) :
    ∀ t : Spec (.of K), p t ∈ ProperSmoothLocus.goodOpen f := by
  intro t
  have h := section_mem_goodOpen_of_smooth_pullback pX pY f p hp hF hn
  simpa only [Subsingleton.elim t (IsLocalRing.closedPoint K)] using h

end M9Native.RationalSectionGoodOpen
