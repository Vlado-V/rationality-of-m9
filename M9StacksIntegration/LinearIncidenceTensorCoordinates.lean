module

public import M9StacksIntegration.LagrangianMatrixChart
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBilinear
public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Sections

/-! Actual tensor-product trivializations and the coefficient formula for the
universal incidence section. All tensor and pullback isomorphisms are the native
ones, and their action on the original sections is retained. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
namespace M9Native.LinearIncidenceTensorCoordinates
open M9Native.LagrangianMatrixChart

abbrev tensorObj (X : Scheme.{u}) (A B : X.Modules) : X.Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj A).obj B)

def tensorTop (X : Scheme.{u}) (A B : X.Modules) (s : Γ(A,⊤)) (t : Γ(B,⊤)) :
    Γ(tensorObj X A B,⊤) :=
  Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op ⊤) A B s t

theorem tensorTop_smul_left (X : Scheme.{u}) (A B : X.Modules) (r : Γ(X,⊤))
    (s : Γ(A,⊤)) (t : Γ(B,⊤)) : tensorTop X A B (r • s) t=r • tensorTop X A B s t := by
  unfold tensorTop Stacks.SheafOfModules.tensorSectionsAt
  exact ((Stacks.SheafOfModules.TensorSheafification.toSheafify X.sheaf.obj
    X.ringCatSheaf.property (PresheafOfModules.tensorObj A.val B.val)).app (op ⊤)).hom.map_smul r (s ⊗ₜ t)

def unitTensorIso (X : Scheme.{u}) (B : X.Modules) :
    tensorObj X (SheafOfModules.unit X.ringCatSheaf) B ≅ B :=
  Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor X.sheaf.obj X.ringCatSheaf.property B

def unitCoordinate (X : Scheme.{u}) (s : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules),⊤)) :
    Γ(X,⊤) := s

/-- The actual native unit-tensor isomorphism multiplies the coefficient section. -/
theorem unitTensor_apply (X : Scheme.{u}) (B : X.Modules) (r : Γ(X,⊤)) (t : Γ(B,⊤)) :
    (unitTensorIso X B).hom.app ⊤
      (tensorTop X (SheafOfModules.unit X.ringCatSheaf) B r t)=r • t := by
  have hr : r=r • (1 : Γ(X,⊤)) := by simp
  calc
    _ = (unitTensorIso X B).hom.app ⊤
        (tensorTop X (SheafOfModules.unit X.ringCatSheaf) B (r • (1 : Γ(X,⊤))) t) := by rw [← hr]
    _ = r • (unitTensorIso X B).hom.app ⊤
        (tensorTop X (SheafOfModules.unit X.ringCatSheaf) B (1 : Γ(X,⊤)) t) := by
      rw [tensorTop_smul_left,Scheme.Modules.Hom.app_smul]
    _ = r • t := by
      rw [tensorTop]
      exact congrArg (fun z => r • z)
        (Stacks.SheafOfModules.tensorSections_leftUnitorAt X.sheaf.obj X.ringCatSheaf.property (op ⊤) B t)

/-- Canonical actual pullback and tensor isomorphisms trivialize a line times a rank-r quotient. -/
def pullbackTensorTrivialization {X Y : Scheme.{u}} (f : X ⟶ Y) (A B : Y.Modules) (r : ℕ)
    (e : (Scheme.Modules.pullback f).obj A ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (d : (Scheme.Modules.pullback f).obj B ≅ freeOn X r) :
    (Scheme.Modules.pullback f).obj (tensorObj Y A B) ≅ freeOn X r :=
  (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f A B) ≪≫
    (Stacks.SheafOfModules.Invertible.tensorProductIso X.sheaf.obj X.ringCatSheaf.property e d) ≪≫
      (unitTensorIso X (freeOn X r))

theorem pullbackTensorTrivialization_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (A B : Y.Modules) (r : ℕ)
    (e : (Scheme.Modules.pullback f).obj A ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (d : (Scheme.Modules.pullback f).obj B ≅ freeOn X r) (s : Γ(A,⊤)) (t : Γ(B,⊤)) :
    (pullbackTensorTrivialization f A B r e d).hom.app ⊤
      (pullbackGlobalSections f (tensorObj Y A B) (tensorTop Y A B s t))=
        (unitCoordinate X (e.hom.app ⊤ (pullbackGlobalSections f A s))) •
          (d.hom.app ⊤ (pullbackGlobalSections f B t)) := by
  refine (congrArg (fun z => (unitTensorIso X (freeOn X r)).hom.app ⊤
      ((Stacks.SheafOfModules.Invertible.tensorProductIso X.sheaf.obj X.ringCatSheaf.property e d).hom.val.app (op ⊤) z))
    (Stacks.PullbackTensorIso.pullbackGlobalSections_tensorSectionsAt f A B s t)).trans ?_
  refine (congrArg (fun z => (unitTensorIso X (freeOn X r)).hom.app ⊤ z)
    (Stacks.SheafOfModules.tensorSections_tensorProductIsoAt X.sheaf.obj X.ringCatSheaf.property
      (op ⊤) _ _ _ _ e d (pullbackGlobalSections f A s) (pullbackGlobalSections f B t))).trans ?_
  exact unitTensor_apply X (freeOn X r) _ _

end M9Native.LinearIncidenceTensorCoordinates
end
