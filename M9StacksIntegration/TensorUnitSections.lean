module

public import M9StacksIntegration.TensorFreeCoordinates
public import M9StacksIntegration.LagrangianSectionGeneration
public import M9StacksIntegration.QuotientSectionMorphism

/-! Actual unit/tensor section identities are proved over an abstract
scheme before any concrete projective-bundle model is substituted. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.presheaf AlgebraicGeometry.Scheme.unitModule
  SheafOfModules.unit PresheafOfModules.unit
  Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
namespace M9Native.TensorUnitSections
open LinearIncidenceTensorCoordinates
def tensorFirst {Y : Scheme.{u}} {A B : Y.Modules} (f : A ⟶ B) (L : Y.Modules) :
    tensorObj Y A L ⟶ tensorObj Y B L :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).flip.obj L).map f

theorem tensorFirst_tensorTop {Y : Scheme.{u}} {A B : Y.Modules} (f : A ⟶ B)
    (L : Y.Modules) (s : Γ(A,⊤)) (t : Γ(L,⊤)) :
    (tensorFirst f L).app ⊤ (tensorTop Y A L s t) =
      tensorTop Y B L (f.app ⊤ s) t := by
  refine (Stacks.SheafOfModules.toSheafify_app_map_obj
    (O := Y.sheaf.obj) (hO := Y.ringCatSheaf.property)
    (f := PresheafOfModules.tensorHom (O := Y.sheaf.obj) f.val (𝟙 L.val))
    (op ⊤) (s ⊗ₜ t)).trans ?_
  exact congrArg (fun z =>
    (Stacks.SheafOfModules.TensorSheafification.toSheafify Y.sheaf.obj Y.ringCatSheaf.property
      (PresheafOfModules.tensorObj B.val L.val)).app (op ⊤) z)
    (PresheafOfModules.tensorHom_tmul (O := Y.sheaf.obj) f.val (𝟙 L.val) (op ⊤) s t)

theorem unitTensor_inv_apply {Y : Scheme.{u}} (L : Y.Modules)
    (c : Γ(Y,⊤)) (t : Γ(L,⊤)) :
    (unitTensorIso Y L).inv.app ⊤ (c • t) =
      tensorTop Y (Scheme.unitModule Y) L c t := by
  apply (ConcreteCategory.bijective_of_isIso ((unitTensorIso Y L).hom.app ⊤)).injective
  have h := congrArg (fun q : L ⟶ L => q.app ⊤ (c • t)) (unitTensorIso Y L).inv_hom_id
  exact h.trans (unitTensor_apply Y L c t).symm

theorem inverse_unit_apply {Y Z : Scheme.{u}} (f : Z ⟶ Y) (c : Γ(Y,⊤)) :
    (Scheme.Modules.pullbackUnitIso f).inv.app ⊤ (f.appTop c) =
      pullbackGlobalSections f (Scheme.unitModule Y) c := by
  have h := congrArg ((Scheme.Modules.pullbackUnitIso f).inv.app ⊤)
    (SectionsEqualizer.pullbackUnitIso_unit f c)
  exact h.symm.trans (congrArg
    (fun q : (Scheme.Modules.pullback f).obj (Scheme.unitModule Y) ⟶
      (Scheme.Modules.pullback f).obj (Scheme.unitModule Y) => q.app ⊤
        (pullbackGlobalSections f (Scheme.unitModule Y) c))
    (Scheme.Modules.pullbackUnitIso f).hom_inv_id)


theorem unit_map_apply {Y : Scheme.{u}} {L : Y.Modules}
    (s : Scheme.unitModule Y ⟶ L) (c : Γ(Y,⊤)) :
    s.app ⊤ c = c • s.app ⊤ (1 : Γ(Y,⊤)) := by
  calc
    _ = s.app ⊤ (c • (1 : Γ(Y,⊤))) := congrArg (s.app ⊤) (by simp)
    _ = _ := Scheme.Modules.Hom.app_smul s c _

theorem unitHom_add {Y : Scheme.{u}} (L : Y.Modules) (s t : Γ(L,⊤)) :
    Scheme.Modules.unitHomEquivTop L (s+t) =
      Scheme.Modules.unitHomEquivTop L s + Scheme.Modules.unitHomEquivTop L t := by
  apply LagrangianSectionGeneration.unitHom_ext_top_one
  calc
    _ = s+t := LagrangianAffineDeterminant.unitHom_top_one L _
    _ = (Scheme.Modules.unitHomEquivTop L s).app ⊤ (1 : Γ(Y,⊤)) +
        (Scheme.Modules.unitHomEquivTop L t).app ⊤ (1 : Γ(Y,⊤)) :=
      (congrArg₂ (·+·) (LagrangianAffineDeterminant.unitHom_top_one L s)
        (LagrangianAffineDeterminant.unitHom_top_one L t)).symm
    _ = _ := rfl

theorem unitHom_tensorTop {Y : Scheme.{u}} (A L : Y.Modules)
    (s : Γ(A,⊤)) (t : Γ(L,⊤)) :
    Scheme.Modules.unitHomEquivTop (tensorObj Y A L) (tensorTop Y A L s t) =
      Scheme.Modules.unitHomEquivTop L t ≫ (unitTensorIso Y L).inv ≫
        tensorFirst (Scheme.Modules.unitHomEquivTop A s) L := by
  apply LagrangianSectionGeneration.unitHom_ext_top_one
  refine (LagrangianAffineDeterminant.unitHom_top_one (tensorObj Y A L) _).trans ?_
  symm
  change (tensorFirst (Scheme.Modules.unitHomEquivTop A s) L).app ⊤
    ((unitTensorIso Y L).inv.app ⊤
      ((Scheme.Modules.unitHomEquivTop L t).app ⊤ (1 : Γ(Y,⊤)))) = _
  have ht := LagrangianAffineDeterminant.unitHom_top_one L t
  rw [ht]
  have hu := unitTensor_inv_apply L (1 : Γ(Y,⊤)) t
  simp only [one_smul] at hu
  rw [hu,tensorFirst_tensorTop]
  exact congrArg (fun z => tensorTop Y A L z t)
    (LagrangianAffineDeterminant.unitHom_top_one A s)

/-- Endomorphisms of the actual unit act centrally on actual pure
unit-to-module tensor maps. -/
theorem unit_tensor_central {Y : Scheme.{u}} (L : Y.Modules)
    (a : Scheme.unitModule Y ⟶ Scheme.unitModule Y) (s : Scheme.unitModule Y ⟶ L) :
    s ≫ (unitTensorIso Y L).inv ≫ tensorFirst a L =
      a ≫ s ≫ (unitTensorIso Y L).inv := by
  apply LagrangianSectionGeneration.unitHom_ext_top_one
  change (tensorFirst a L).app ⊤
      ((unitTensorIso Y L).inv.app ⊤ (s.app ⊤ (1 : Γ(Y,⊤)))) =
    (unitTensorIso Y L).inv.app ⊤ (s.app ⊤ (a.app ⊤ (1 : Γ(Y,⊤))))
  have hu := unitTensor_inv_apply L (1 : Γ(Y,⊤)) (s.app ⊤ (1 : Γ(Y,⊤)))
  simp only [one_smul] at hu
  rw [hu,tensorFirst_tensorTop]
  change tensorTop Y (Scheme.unitModule Y) L
      (Stacks.FreeSheafMatrix.unitEndValue a) (s.app ⊤ (1 : Γ(Y,⊤))) =
    (unitTensorIso Y L).inv.app ⊤ (s.app ⊤ (Stacks.FreeSheafMatrix.unitEndValue a))
  exact (unitTensor_inv_apply L (Stacks.FreeSheafMatrix.unitEndValue a) _).symm.trans
    (congrArg ((unitTensorIso Y L).inv.app ⊤)
      (unit_map_apply s (Stacks.FreeSheafMatrix.unitEndValue a)).symm)

end M9Native.TensorUnitSections
