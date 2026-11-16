module

public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.ModuliFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismCancellation
public import M9StacksIntegration.CoarseQuasiCompactTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStack
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic

@[expose] public section

/-! Structural local finite type and quasi-compactness of the genuine coarse
target.  Source hypotheses are kept separate so actual curve-stack producers
can discharge them; no target variety property is supplied as a premise. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9Native.CoarseFiniteTypeTarget

universe u

variable (B : BigFppfSite.{u}) (K : Type u) [Field K]
  (hK : B.Contains (Spec (.of K)))

/-- The structural local-finite-type property of the actual categorical
target follows from finite inertia and structural local finite type of its
source.  The output uses the same native base morphism as the all-test
variety adapter. -/
theorem locallyFiniteType_of_categorical
    (X : Stack.AlgebraicStacks.{u, u + 1} B (Spec (.of K)) hK)
    (Y : AlgebraicSpaces B (Spec (.of K)) hK)
    (f : X ⟶ Stack.algebraicSpaceStack.{u, u + 1} B (Spec (.of K)) hK Y.obj Y.property)
    (hf : Stack.IsCategoricalModuliSpace B (Spec (.of K)) hK Y f.hom)
    (hI : Stack.AlgebraicStacks.IsFinite B (Spec (.of K)) hK
      (Stack.inertiaProjectionAlgebraicStacks B (Spec (.of K)) hK X))
    (hX : Stack.AlgebraicStacks.IsLocallyOfFiniteType B (Spec (.of K)) hK
      (Stack.structureMorphism B (Spec (.of K)) hK X)) :
    Space.IsLocallyOfFiniteType B (Spec (.of K)) hK
      ((Space.isTerminal_yoneda_obj_base B (Spec (.of K)) hK).from Y.obj) := by
  let U : BigFppfOver B (Spec (.of K)) hK := Over.mk (𝟙 (B.obj hK))
  let A : AlgebraicSpaces B (Spec (.of K)) hK :=
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B (Spec (.of K)) hK U⟩
  let q : Y ⟶ A := ObjectProperty.homMk
    ((Space.isTerminal_yoneda_obj_base B (Spec (.of K)) hK).from Y.obj)
  let p : X ⟶ Stack.algebraicSpaceStack.{u, u + 1} B (Spec (.of K)) hK A.obj A.property :=
    f ≫ Stack.algebraicSpaceStackMap.{u, u + 1} B (Spec (.of K)) hK
      Y.property A.property q.hom
  have hA : Space.HasEtaleLocalProperty B (Spec (.of K)) hK A.obj
      (fun T : Scheme.{u} => IsLocallyNoetherian T) := by
    apply (Space.exists_atlas_iff_of_representable B (Spec (.of K)) hK A.obj
      (fun T : Scheme.{u} => IsLocallyNoetherian T) U (Iso.refl _)).2
    change IsLocallyNoetherian (Spec (.of K))
    infer_instance
  have hp : Stack.AlgebraicStacks.IsLocallyOfFiniteType B (Spec (.of K)) hK p := by
    apply Stack.AlgebraicStacks.isLocallyOfFiniteType_of_comp B (Spec (.of K)) hK p
      (Stack.structureMorphism B (Spec (.of K)) hK _)
    simpa only [Stack.comp_structureMorphism] using hX
  exact (Stack.isLocallyOfFiniteType_of_isCategoricalModuliSpace_of_isFinite_inertia
    B (Spec (.of K)) hK X hI A hA p hp Y f hf).2 q ⟨Iso.refl _⟩

export M9Native.CoarseQuasiCompactTarget (quasiCompact_of_stack quasiCompact_of_surjective)

end M9Native.CoarseFiniteTypeTarget
