module

public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus

@[expose] public section

/-! The elementary open-substack compactness argument from the native
OpenSubstackDenseTestProper provider, isolated from its unrelated valuative
criterion dependencies.  The actual point maps and their topologies are used. -/

open CategoryTheory AlgebraicGeometry Topology

namespace M9Native.OpenSubstackQuasiCompact

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Stack.AlgebraicStacks.{u, w} B S hS}

private theorem inclusion_openEmbedding (V : Stack.OpenSubstack X) :
    @IsOpenEmbedding _ _ (Stack.pointTopology B S hS V.toAlgebraicStack.val)
      (Stack.pointTopology B S hS X.val)
      (Stack.AlgebraicStacks.pointsMap B S hS V.inclusion) := by
  let := Stack.pointTopology B S hS V.toAlgebraicStack.val
  let := Stack.pointTopology B S hS X.val
  exact IsOpenEmbedding.of_continuous_injective_isOpenMap
    (Stack.continuous_pointsMap B S hS _ _ V.inclusion.hom.hom)
    (Stack.pointsMap_injective_of_fullyFaithful B S hS V.inclusion)
    (Stack.AlgebraicStacks.isOpenMap_pointsMap_of_isOpenImmersion B S hS
      V.inclusion V.isOpenImmersion)

/-- A genuine open substack of a quasi-compact locally Noetherian open
substack is quasi-compact. -/
theorem quasiCompact_of_le (V W : Stack.OpenSubstack X)
    (hle : V.property ≤ W.property)
    (hqc : Stack.IsQuasiCompactStack.{u, w} B S hS W.toAlgebraicStack.val
      W.toAlgebraicStack.property)
    (hN : Stack.HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) W.toAlgebraicStack) :
    Stack.IsQuasiCompactStack.{u, w} B S hS V.toAlgebraicStack.val
      V.toAlgebraicStack.property := by
  let := Stack.pointTopology B S hS V.toAlgebraicStack.val
  let := Stack.pointTopology B S hS W.toAlgebraicStack.val
  let := Stack.pointTopology B S hS X.val
  have := Stack.AlgebraicStacks.noetherianSpace_points_of_isQuasiCompactStack
    B S hS W.toAlgebraicStack hqc hN
  let f : V.toAlgebraicStack ⟶ W.toAlgebraicStack :=
    W.factor B S hS V.inclusion (fun x => hle _ x.property)
  have hcomp : f ≫ W.inclusion = V.inclusion := rfl
  have hf : IsInducing (Stack.AlgebraicStacks.pointsMap B S hS f) :=
    .of_comp (Stack.continuous_pointsMap B S hS _ _ f.hom.hom)
      (inclusion_openEmbedding B S hS W).continuous
      (by
        rw [← Stack.AlgebraicStacks.pointsMap_comp, hcomp]
        exact (inclusion_openEmbedding B S hS V).isInducing)
  exact ⟨hf.isCompact_iff.2 (TopologicalSpace.NoetherianSpace.isCompact _)⟩

end M9Native.OpenSubstackQuasiCompact
