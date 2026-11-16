module

public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliSeparation.DiagonalDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliSeparation.SpaceSeparationBridge
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalHomeomorphism

@[expose] public section

/-! Relative separation of the original target of a universal homeomorphism from
a separated algebraic stack.  This uses actual diagonal descent over the given
base, without changing the target or assuming it separated. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9Native.CoarseSeparatedTarget

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The target of a universal homeomorphism from a separated algebraic stack is
separated over the same base. -/
theorem separated_of_universalHomeomorphism
    (X : Stack.AlgebraicStacks.{u, w} B S hS)
    (Y : AlgebraicSpaces B S hS)
    (f : X ⟶ Stack.algebraicSpaceStack.{u, w} B S hS Y.obj Y.property)
    (hf : Stack.AlgebraicStacks.UniversalHomeomorphism B S hS f)
    (hX : Stack.AlgebraicStacks.IsSeparated B S hS
      (Stack.structureMorphism B S hS X)) :
    Space.IsSeparatedOver B S hS Y.obj := by
  have hUC : Stack.AlgebraicStacks.UniversallyClosed B S hS f := by
    intro Z g
    letI := Stack.pointTopology B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val
    letI := Stack.pointTopology B S hS Z.val
    exact (hf Z g).isClosedMap
  have hsurj : Stack.IsSurjective B S hS f := by
    let C := Stack.twoFibreProductSquareAlgebraicStacks B S hS (𝟙 _) f
    have h : Function.Surjective (Stack.AlgebraicStacks.pointsMap B S hS C.fst) := by
      letI := Stack.pointTopology B S hS C.pt.val
      letI := Stack.pointTopology B S hS
        (Stack.algebraicSpaceStack.{u, w} B S hS Y.obj Y.property).val
      exact (hf _ (𝟙 _)).surjective
    have hc := Stack.AlgebraicStacks.pointsMap_eq_of_hom₂ B S hS C.iso.hom
    rw [Category.comp_id, Stack.AlgebraicStacks.pointsMap_comp] at hc
    rw [hc] at h
    exact h.of_comp
  let p := Stack.structureMorphism B S hS
    (Stack.algebraicSpaceStack.{u, w} B S hS Y.obj Y.property)
  have hDelta : Stack.AlgebraicStacks.UniversallyClosed B S hS
      (Stack.relativeDiagonalAlgebraicStacks B S hS (f ≫ p)) := by
    rw [Stack.comp_structureMorphism]
    exact Stack.AlgebraicStacks.universallyClosed_relativeDiagonalAlgebraicStacks_of_isSeparated
      B S hS _ hX
  exact Stack.isSeparatedOver_of_universallyClosed_relativeDiagonal B S hS Y.property
    (Stack.AlgebraicStacks.universallyClosed_relativeDiagonal_of_comp B S hS f p
      hUC hsurj hDelta)

/-- The same statement in the choice-independent form of universal
homeomorphism exported by the actual Keel--Mori constructor. -/
theorem separated_of_coarse_universalHomeomorphism
    (X : Stack.AlgebraicStacks.{u, w} B S hS)
    (Y : AlgebraicSpaces B S hS)
    (f : X ⟶ Stack.algebraicSpaceStack.{u, w} B S hS Y.obj Y.property)
    (hf : Stack.UniversalHomeomorphism B S hS f)
    (hX : Stack.IsSeparatedOver B S hS X) :
    Space.IsSeparatedOver B S hS Y.obj :=
  separated_of_universalHomeomorphism B S hS X Y f
    (fun Z g => hf Z g (Stack.twoFibreProductSquareAlgebraicStacks B S hS g f)
      (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS g f)) hX

end M9Native.CoarseSeparatedTarget
