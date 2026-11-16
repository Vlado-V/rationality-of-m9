module

public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStack
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic

@[expose] public section

/-! Quasi-compactness of the original algebraic-space target of a genuinely
surjective morphism from a quasi-compact stack. The actual native comparison
of point topologies is used; no target compactness or field-point quotient
identification is supplied as a premise. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9Native.CoarseQuasiCompactTarget

universe u

variable (B : BigFppfSite.{u}) (K : Type u) [Field K]
  (hK : B.Contains (Spec (.of K)))

/-- The original algebraic space is quasi-compact whenever its actual stack of
points is.  This is the genuine native homeomorphism of point spaces. -/
theorem quasiCompact_of_stack
    (Y : AlgebraicSpaces B (Spec (.of K)) hK)
    (hY : Stack.IsQuasiCompactStack.{u, u + 1} B (Spec (.of K)) hK
      (Stack.algebraicSpaceStack.{u, u + 1} B (Spec (.of K)) hK Y.obj Y.property).val
      (Stack.algebraicSpaceStack.{u, u + 1} B (Spec (.of K)) hK Y.obj Y.property).property) :
    Space.IsQuasiCompactSpace B (Spec (.of K)) hK Y.obj := by
  let := Space.pointTopology B (Spec (.of K)) hK Y.obj
  let := Stack.pointTopology B (Spec (.of K)) hK
    (Stack.algebraicSpaceStack.{u, u + 1} B (Spec (.of K)) hK Y.obj Y.property).val
  let : CompactSpace (Stack.AlgebraicStacks.points B (Spec (.of K)) hK
      (Stack.algebraicSpaceStack.{u, u + 1} B (Spec (.of K)) hK Y.obj Y.property)) := hY
  let e := (Stack.isHomeomorph_spacePointMap_representing B (Spec (.of K)) hK
    Y.obj Y.property
    (Stack.algebraicSpaceStack.{u, u + 1} B (Spec (.of K)) hK Y.obj Y.property).val
    (StacksRepresentableCFG.EquivalenceOver.refl _)).homeomorph _
  have hCompact : CompactSpace (Space.points B (Spec (.of K)) hK Y.obj) := e.symm.compactSpace
  exact (Space.isQuasiCompactSpace_iff_compactSpace_points B (Spec (.of K)) hK
    Y.obj Y.property).2 hCompact

/-- Quasi-compactness transfers along an actual surjective coarse morphism;
only quasi-compactness of the genuine source is assumed. -/
theorem quasiCompact_of_surjective
    (X : Stack.AlgebraicStacks.{u, u + 1} B (Spec (.of K)) hK)
    (Y : AlgebraicSpaces B (Spec (.of K)) hK)
    (f : X ⟶ Stack.algebraicSpaceStack.{u, u + 1} B (Spec (.of K)) hK Y.obj Y.property)
    (hf : Stack.IsSurjective B (Spec (.of K)) hK f)
    (hX : Stack.IsQuasiCompactStack.{u, u + 1} B (Spec (.of K)) hK X.val X.property) :
    Space.IsQuasiCompactSpace B (Spec (.of K)) hK Y.obj :=
  quasiCompact_of_stack B K hK Y
    (Stack.isQuasiCompactStack_of_isSurjective B (Spec (.of K)) hK f hX hf)


end M9Native.CoarseQuasiCompactTarget
