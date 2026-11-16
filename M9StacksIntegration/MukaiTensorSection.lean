module

public import M9StacksIntegration.MukaiExtEvaluation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorUnitSections

/-!
# The actual natural tensor section and its adjunction evaluation

The explicit native unitors are assembled naturally on local pure
tensors. An actual section of a bundle then gives a natural map
`Id ⟶ (- tensor F)`. Its adjunction evaluation is computed on actual
local sections, so it can be compared with the actual wedge morphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace M9Native.MukaiTensorSection

open M9Native.MukaiCupAlternating M9Native.MukaiHomExact
open M9Native.MukaiExtEvaluation

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable {X : Scheme.{u}}

/-- The explicit native unitor on the actual tensor sheaf. -/
abbrev unitRightIso (M : X.Modules) :
    (tensorRight (_root_.SheafOfModules.unit X.ringCatSheaf)).obj M ≅ M :=
  Stacks.SheafOfModules.tensorSheafUnitRightIso X.sheaf.obj X.ringCatSheaf.property M

/-- The actual native unitor is natural, verified on local pure tensors. -/
theorem unitRightIso_naturality {M N : X.Modules} (g : M ⟶ N) :
    (tensorRight (_root_.SheafOfModules.unit X.ringCatSheaf)).map g ≫ (unitRightIso N).hom =
      (unitRightIso M).hom ≫ g := by
  apply PresheafOfModules.tensorSheaf_hom_ext
  intro U m r
  rw [_root_.SheafOfModules.comp_val_app_apply,
    _root_.SheafOfModules.comp_val_app_apply]
  refine Eq.trans (congrArg (fun z => (unitRightIso N).hom.val.app U z)
    (tensorRight_map_unit (_root_.SheafOfModules.unit X.ringCatSheaf) g U m r)) ?_
  exact (Stacks.SheafOfModules.tensorSheafUnitRightIso_hom_toSheafify_tmul
      X.sheaf.obj X.ringCatSheaf.property N U (g.val.app U m) r).trans
    (((g.val.app U).hom.map_smul r m).symm.trans
      (congrArg (fun z => g.val.app U z)
        (Stacks.SheafOfModules.tensorSheafUnitRightIso_hom_toSheafify_tmul
          X.sheaf.obj X.ringCatSheaf.property M U m r).symm))

/-- The actual explicit tensor-unit maps form a genuine natural
isomorphism to the identity functor. -/
def tensorUnitNatIso :
    tensorRight (_root_.SheafOfModules.unit X.ringCatSheaf) ≅ 𝟭 X.Modules :=
  NatIso.ofComponents unitRightIso (fun g => unitRightIso_naturality g)

/-- An actual bundle section gives an actual natural tensor section. -/
def tensorSection (F : X.Modules) (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ F) :
    𝟭 X.Modules ⟶ tensorRight F :=
  tensorUnitNatIso.inv ≫ tensorBySection F s

/-- Its value on an actual local section is the actual pure tensor by
the original section of the bundle. -/
theorem tensorSection_app (F : X.Modules)
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ F)
    (M : X.Modules) (U : X.Opensᵒᵖ) (m : M.val.obj U) :
    ((tensorSection F s).app M).val.app U m =
      (PresheafOfModules.tensorSheafUnit M F).app U
        (m ⊗ₜ (F.unitHomEquiv s).val U) := by
  change (((tensorUnitNatIso (X := X)).inv.app M) ≫
    (tensorBySection F s).app M).val.app U m = _
  rw [_root_.SheafOfModules.comp_val_app_apply]
  refine Eq.trans (congrArg (fun z => ((tensorBySection F s).app M).val.app U z)
    (Stacks.SheafOfModules.tensorSheafUnitRightIso_inv_app
      X.sheaf.obj X.ringCatSheaf.property M U m)) ?_
  have h := Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
    X.sheaf M (_root_.SheafOfModules.unit X.ringCatSheaf) (𝟙 M) s U m
      (1 : X.ringCatSheaf.obj.obj U)
  have hid : ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map (𝟙 M)).app
      (_root_.SheafOfModules.unit X.ringCatSheaf) = 𝟙 _ :=
    NatTrans.congr_app ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map_id M) _
  rw [hid, Category.id_comp] at h
  exact h

/-- Native currying evaluated over the same open is actual evaluation
of the original tensor morphism on the actual pure tensor. -/
theorem transpose_on_local_tensor (A F W : X.Modules)
    (b : (tensorRight F).obj A ⟶ W) (U : X.Opensᵒᵖ)
    (a : A.val.obj U) (x : F.val.obj U) :
    Stacks.SheafOfModules.evalSection X.sheaf.obj F.val W.val U
        (((Stacks.SheafOfModules.InternalHom.sheafTensorRightHomAdjunction X.sheaf F).homEquiv
          A W b).val.app U a) x =
      b.val.app U ((PresheafOfModules.tensorSheafUnit A F).app U (a ⊗ₜ x)) := by
  have h := Stacks.SheafOfModules.InternalHom.sheafTensorHomEquiv_apply
    X.sheaf A F W b U.unop a (𝟙 U.unop) x
  have ha : A.val.restrictₛₗ (𝟙 U.unop).op a = a := by
    change A.val.map (𝟙 U) a = a
    simp
  change _ = b.val.app U ((PresheafOfModules.tensorSheafUnit A F).app U
    (A.val.restrictₛₗ (𝟙 U.unop).op a ⊗ₜ x)) at h
  exact h.trans (congrArg (fun z => b.val.app U
    ((PresheafOfModules.tensorSheafUnit A F).app U (z ⊗ₜ x))) ha)

/-- The genuine tensor-Hom counit evaluates a genuine local morphism. -/
theorem counit_on_local_tensor (F W : X.Modules) (U : X.Opensᵒᵖ)
    (a : ((homFunctor F).obj W).val.obj U) (x : F.val.obj U) :
    ((Stacks.SheafOfModules.InternalHom.sheafTensorRightHomAdjunction X.sheaf F).counit.app W).val.app U
        ((PresheafOfModules.tensorSheafUnit ((homFunctor F).obj W) F).app U (a ⊗ₜ x)) =
      Stacks.SheafOfModules.evalSection X.sheaf.obj F.val W.val U a x := by
  let adj : tensorRight F ⊣ homFunctor F :=
    Stacks.SheafOfModules.InternalHom.sheafTensorRightHomAdjunction X.sheaf F
  have h := transpose_on_local_tensor ((homFunctor F).obj W) F W (adj.counit.app W) U a x
  have hc : adj.homEquiv ((homFunctor F).obj W) W (adj.counit.app W) = 𝟙 _ :=
    adj.right_triangle_components W
  rw [hc] at h
  exact h.symm

/-- The actual adjunction evaluation induced by an actual section is
literal evaluation at that section, on every open. -/
theorem adjunctionEvaluation_app (F W : X.Modules)
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ F)
    (U : X.Opensᵒᵖ) (a : ((homFunctor F).obj W).val.obj U) :
    (adjunctionEvaluation
      (Stacks.SheafOfModules.InternalHom.sheafTensorRightHomAdjunction X.sheaf F)
      (tensorSection F s) W).val.app U a =
      Stacks.SheafOfModules.evalSection X.sheaf.obj F.val W.val U a ((F.unitHomEquiv s).val U) := by
  rw [adjunctionEvaluation, _root_.SheafOfModules.comp_val_app_apply]
  refine Eq.trans (congrArg (fun z =>
    ((Stacks.SheafOfModules.InternalHom.sheafTensorRightHomAdjunction X.sheaf F).counit.app W).val.app U z)
      (tensorSection_app F s ((homFunctor F).obj W) U a)) ?_
  exact counit_on_local_tensor F W U a ((F.unitHomEquiv s).val U)

end M9Native.MukaiTensorSection
