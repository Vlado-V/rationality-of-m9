module

public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStackChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactQuasiSeparatedStack
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStackInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationChangeOfBase

@[expose] public section

/-! Quasi-compactness for the actual native strict change of base.  The proof
uses the genuine two-fibre-product comparison and an actual compact base
scheme, rather than a field-point comparison. -/

open CategoryTheory AlgebraicGeometry

namespace M9Native.QuasiCompactStackBaseChange

universe u w

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u})
  (hS : B.Contains S) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')

/-- A quasi-compact stack over a quasi-separated base remains quasi-compact
after actual change of base to a compact scheme. -/
theorem quasiCompact_changeOfBase
    (hqs : QuasiSeparatedSpace S') (hSCompact : CompactSpace S)
    (X : Stack.AlgebraicStacks.{u, w} B S' hS')
    (hX : Stack.IsQuasiCompactStack.{u, w} B S' hS' X.val X.property) :
    Stack.IsQuasiCompactStack.{u, w} B S hS
      (Stack.changeOfBase B S S' hS hS' g X).val
      (Stack.changeOfBase B S S' hS hS' g X).property := by
  obtain ⟨W⟩ := Stack.changeOfBase_twoFibreProductWitness B S S' hS hS' g X
  have hstructure := Stack.isQuasiCompactMorphism_structureMorphism B S' hS' hqs X hX
  have hf : Stack.IsQuasiCompactMorphism B S' hS' W.f := by
    rw [Stack.AlgebraicStacks.witness_f_eq_structure B S S' hS hS' g X W]
    exact hstructure
  have hSStack : Stack.IsQuasiCompactStack.{u, w} B S' hS'
      (Stack.schemeStack.{u, w} B S' hS' (Over.mk g)).val
      (Stack.schemeStack.{u, w} B S' hS' (Over.mk g)).property :=
    Stack.isQuasiCompactStack_schemeStack_of_compactSpace.{u, w}
      B S' hS' (Over.mk g) hSCompact
  have hcanonical := hf _ W.k hSStack
  have hW : Stack.IsQuasiCompactStack.{u, w} B S' hS'
      W.square.pt.val W.square.pt.property :=
    Stack.isQuasiCompactStack_of_isTwoFibreProduct B S' hS'
      (Bicategory.isTwoFibreProduct_swap
        (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S' hS' W.k W.f))
      W.isTwoFibreProduct hcanonical
  have hpt : W.square.pt =
      Stack.changeBaseAlgebraicStack B S S' hS hS' g
        (Stack.changeOfBase B S S' hS hS' g X) := W.pt_eq
  have hview : Stack.IsQuasiCompactStack.{u, w} B S' hS'
      (Stack.changeBaseAlgebraicStack B S S' hS hS' g
        (Stack.changeOfBase B S S' hS hS' g X)).val
      (Stack.changeBaseAlgebraicStack B S S' hS hS' g
        (Stack.changeOfBase B S S' hS hS' g X)).property := by
    exact hpt ▸ hW
  exact (Stack.isQuasiCompactStack_changeBaseAlgebraicStack_iff B S S' hS hS' g _).1 hview

end M9Native.QuasiCompactStackBaseChange
