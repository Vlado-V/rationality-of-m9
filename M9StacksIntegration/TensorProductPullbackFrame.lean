module

public import M9StacksIntegration.LinearIncidenceTensorCoordinates

/-! The native pullback-tensor comparison with arbitrary actual
frames of both factors, retaining the pure-tensor section formula. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
namespace M9Native.TensorProductPullbackFrame
open LinearIncidenceTensorCoordinates

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (A B : Y.Modules) (C D : X.Modules)
  (a : (Scheme.Modules.pullback f).obj A ≅ C)
  (b : (Scheme.Modules.pullback f).obj B ≅ D)

def frame : (Scheme.Modules.pullback f).obj (tensorObj Y A B) ≅ tensorObj X C D :=
  Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f A B ≪≫
    Stacks.SheafOfModules.Invertible.tensorProductIso X.sheaf.obj X.ringCatSheaf.property a b

theorem frame_apply (s : Γ(A,⊤)) (t : Γ(B,⊤)) :
    (frame f A B C D a b).hom.app ⊤
      (pullbackGlobalSections f (tensorObj Y A B) (tensorTop Y A B s t)) =
      tensorTop X C D (a.hom.app ⊤ (pullbackGlobalSections f A s))
        (b.hom.app ⊤ (pullbackGlobalSections f B t)) := by
  refine (congrArg (fun z =>
    (Stacks.SheafOfModules.Invertible.tensorProductIso X.sheaf.obj
      X.ringCatSheaf.property a b).hom.val.app (op ⊤) z)
    (Stacks.PullbackTensorIso.pullbackGlobalSections_tensorSectionsAt f A B s t)).trans ?_
  exact Stacks.SheafOfModules.tensorSections_tensorProductIsoAt X.sheaf.obj
    X.ringCatSheaf.property (op ⊤) _ _ _ _ a b
      (pullbackGlobalSections f A s) (pullbackGlobalSections f B t)

end M9Native.TensorProductPullbackFrame
