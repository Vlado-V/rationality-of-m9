module

public import M9StacksIntegration.LinearIncidenceTensorCoordinates

/-!
# A right line frame for an arbitrary pulled-back module

The actual native pullback-tensor comparison and tensor-product isomorphism
identify a pulled tensor product with its arbitrary first factor when the
second factor has an actual unit frame. The section formula retains the
original tensor sections and canonical pullbacks on arbitrary schemes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

universe u

namespace M9Native.RightLineTensorFrame

open M9Native.LinearIncidenceTensorCoordinates

/-- Native symmetry followed by the native left unitor removes a right unit factor. -/
def rightUnitTensorIso (X : Scheme.{u}) (Q : X.Modules) :
    tensorObj X Q (SheafOfModules.unit X.ringCatSheaf) ≅ Q :=
  (Stacks.SheafOfModules.Invertible.tensorProductBraiding X.sheaf.obj
    X.ringCatSheaf.property Q (SheafOfModules.unit X.ringCatSheaf)) ≪≫
      unitTensorIso X Q

theorem rightUnitTensorIso_apply (X : Scheme.{u}) (Q : X.Modules)
    (s : Γ(Q, ⊤)) (r : Γ(X, ⊤)) :
    (rightUnitTensorIso X Q).hom.app ⊤
      (tensorTop X Q (SheafOfModules.unit X.ringCatSheaf) s r) = r • s := by
  refine (congrArg (fun z => (unitTensorIso X Q).hom.app ⊤ z)
    (Stacks.SheafOfModules.tensorSections_braidingAt X.sheaf.obj X.ringCatSheaf.property
      (op ⊤) Q (SheafOfModules.unit X.ringCatSheaf) s r)).trans ?_
  exact unitTensor_apply X Q r s

/-- The original tensor product is framed using an arbitrary first-factor isomorphism. -/
def frame {X Y : Scheme.{u}} (f : X ⟶ Y) (A B : Y.Modules) (Q : X.Modules)
    (d : (Scheme.Modules.pullback f).obj A ≅ Q)
    (e : (Scheme.Modules.pullback f).obj B ≅
      (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :
    (Scheme.Modules.pullback f).obj (tensorObj Y A B) ≅ Q :=
  (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f A B) ≪≫
    (Stacks.SheafOfModules.Invertible.tensorProductIso X.sheaf.obj X.ringCatSheaf.property d e) ≪≫
      rightUnitTensorIso X Q

/-- The genuine frame takes the actual pulled tensor section to the scalar multiple of
the actual pulled first section, over the actual global-section commutative ring. -/
theorem frame_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (A B : Y.Modules) (Q : X.Modules)
    (d : (Scheme.Modules.pullback f).obj A ≅ Q)
    (e : (Scheme.Modules.pullback f).obj B ≅
      (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (s : Γ(A, ⊤)) (t : Γ(B, ⊤)) :
    (frame f A B Q d e).hom.app ⊤
      (pullbackGlobalSections f (tensorObj Y A B) (tensorTop Y A B s t)) =
        unitCoordinate X (e.hom.app ⊤ (pullbackGlobalSections f B t)) •
          d.hom.app ⊤ (pullbackGlobalSections f A s) := by
  refine (congrArg (fun z => (rightUnitTensorIso X Q).hom.app ⊤
      ((Stacks.SheafOfModules.Invertible.tensorProductIso X.sheaf.obj
        X.ringCatSheaf.property d e).hom.val.app (op ⊤) z))
    (Stacks.PullbackTensorIso.pullbackGlobalSections_tensorSectionsAt f A B s t)).trans ?_
  refine (congrArg (fun z => (rightUnitTensorIso X Q).hom.app ⊤ z)
    (Stacks.SheafOfModules.tensorSections_tensorProductIsoAt X.sheaf.obj X.ringCatSheaf.property
      (op ⊤) _ _ _ _ d e (pullbackGlobalSections f A s)
        (pullbackGlobalSections f B t))).trans ?_
  exact rightUnitTensorIso_apply X Q _ _

end M9Native.RightLineTensorFrame

end
