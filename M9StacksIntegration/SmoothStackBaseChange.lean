module

public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocusChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStackBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbe

@[expose] public section

/-! Smoothness of the actual strict change-of-base stack, and reducedness over a
field.  The comparison uses the genuine two-fibre-product witness for change
of base, not an assumed presentation of its field-valued points. -/

open CategoryTheory AlgebraicGeometry

namespace M9Native.SmoothStackBaseChange

universe u w

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u})
  (hS : B.Contains S) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS')

/-- Smoothness of a stack's structure morphism survives the actual native
change of base. -/
theorem smooth_changeOfBase
    (X : Stack.AlgebraicStacks.{u, w} B S' hS')
    (hX : Stack.AlgebraicStacks.IsSmooth B S' hS'
      (Stack.structureMorphism B S' hS' X)) :
    Stack.AlgebraicStacks.IsSmooth B S hS
      (Stack.structureMorphism B S hS (Stack.changeOfBase B S S' hS hS' g X)) := by
  obtain ⟨W⟩ := Stack.changeOfBase_twoFibreProductWitness B S S' hS hS' g X
  have hf : Stack.AlgebraicStacks.IsSmooth B S' hS' W.f := by
    rw [Stack.AlgebraicStacks.witness_f_eq_structure B S S' hS hS' g X W]
    exact hX
  have hsnd := Stack.AlgebraicStacks.isSmooth_baseChange B S' hS' W.f W.k
    W.square.swap (Bicategory.isTwoFibreProduct_swap W.isTwoFibreProduct) hf
  have hview : Stack.AlgebraicStacks.IsSmooth B S' hS'
      (Stack.changeBaseStructureMorphism B S S' hS hS' g
        (Stack.changeOfBase B S S' hS hS' g X)) :=
    Stack.AlgebraicStacks.property_of_heq
      (fun {A C : Stack.AlgebraicStacks.{u, w} B S' hS'} (f : A ⟶ C) =>
        Stack.AlgebraicStacks.IsSmooth B S' hS' f) W.pt_eq
      (Stack.AlgebraicStacks.heq_mkHom B S' hS'
        (𝒴 := Stack.schemeStack B S' hS' (Over.mk g)) W.pt_eq W.snd_eq) hsnd
  exact (Stack.isSmooth_structureMorphism_iff_changeBase B S S' hS hS' g _).2 hview

/-- A smooth morphism with genuinely reduced target has reduced source. -/
theorem reduced_of_smooth
    {X Y : Stack.AlgebraicStacks.{u, w} B S hS} (f : X ⟶ Y)
    (hf : Stack.AlgebraicStacks.IsSmooth B S hS f)
    (hY : Stack.IsReducedStack B S hS Y) :
    Stack.IsReducedStack B S hS X := by
  refine (Stack.exists_scheme_atlas_iff_forall_scheme B S hS
    (fun T : Scheme.{u} => IsReduced T) X).2 (fun V a ha => ?_)
  exact (Stack.exists_scheme_atlas_iff_forall_scheme B S hS
    (fun T : Scheme.{u} => IsReduced T) Y).1 hY V (a ≫ f)
      (Stack.AlgebraicStacks.isSmooth_comp B S hS a f ha hf)

/-- Over the original field, smoothness of the actual structure morphism
implies reducedness of the stack. -/
theorem reduced_over_field (K : Type u) [Field K]
    (hK : B.Contains (Spec (.of K)))
    (X : Stack.AlgebraicStacks.{u, w} B (Spec (.of K)) hK)
    (hX : Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (Stack.structureMorphism B (Spec (.of K)) hK X)) :
    Stack.IsReducedStack B (Spec (.of K)) hK X := by
  apply reduced_of_smooth B (Spec (.of K)) hK
    (Stack.structureMorphism B (Spec (.of K)) hK X) hX
  apply (Stack.exists_scheme_atlas_iff_scheme B (Spec (.of K)) hK
    (fun T : Scheme.{u} => IsReduced T) (Over.mk (𝟙 (B.obj hK)))).2
  change IsReduced (Spec (.of K))
  infer_instance

end M9Native.SmoothStackBaseChange
