module

public import M9StacksIntegration.MukaiTensorSection

/-!
# The actual section and the tensor-extension wedge diagonal

The explicit left unitor identifies the natural tensor section at the
structure sheaf with the original genuine section. The checked wedge
diagonal is then transported through the actual right unitor, so its
source is the original object rather than a tensor by the unit.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u w

namespace M9Native.MukaiTensorDiagonal

open M9Native.MukaiCupAlternating M9Native.MukaiTensorSection

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable {X : Scheme.{u}}

/-- The explicit native left unitor, typed over the original scheme. -/
abbrev unitLeftIso (F : X.Modules) :
    (tensorRight F).obj (_root_.SheafOfModules.unit X.ringCatSheaf) ≅ F :=
  Stacks.SheafOfModules.tensorSheafUnitLeftIso X.sheaf.obj X.ringCatSheaf.property F

/-- The actual natural tensor section becomes the original section
under the actual left unitor. -/
theorem tensorSection_unit_comp (F : X.Modules)
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ F) :
    (tensorSection F s).app (_root_.SheafOfModules.unit X.ringCatSheaf) ≫
      (unitLeftIso F).hom = s := by
  apply F.unitHomEquiv.injective
  ext U
  change (unitLeftIso F).hom.val.app U
    (((tensorSection F s).app (_root_.SheafOfModules.unit X.ringCatSheaf)).val.app U
      (1 : X.ringCatSheaf.obj.obj U)) = (F.unitHomEquiv s).val U
  refine Eq.trans (congrArg (fun z => (unitLeftIso F).hom.val.app U z)
    (tensorSection_app F s (_root_.SheafOfModules.unit X.ringCatSheaf) U
      (1 : X.ringCatSheaf.obj.obj U))) ?_
  exact (Stacks.SheafOfModules.tensorSheafUnitLeftIso_hom_toSheafify_tmul
      X.sheaf.obj X.ringCatSheaf.property F U
      (1 : X.ringCatSheaf.obj.obj U) ((F.unitHomEquiv s).val U)).trans (one_smul _ _)

/-- The original section determines the actual natural tensor section
at the unit, with its exact source and target. -/
theorem tensorSection_unit_eq (F : X.Modules)
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ F) :
    (tensorSection F s).app (_root_.SheafOfModules.unit X.ringCatSheaf) =
      s ≫ (unitLeftIso F).inv := by
  apply (cancel_mono (unitLeftIso F).hom).mp
  rw [Category.assoc, (unitLeftIso F).inv_hom_id, Category.comp_id]
  exact tensorSection_unit_comp F s

/-- Every genuine section of `O tensor F` is the natural tensor section
of its actual image in `F`. -/
theorem section_eq_tensorSection (F : X.Modules)
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶
      (tensorRight F).obj (_root_.SheafOfModules.unit X.ringCatSheaf)) :
    (tensorSection F (s ≫ (unitLeftIso F).hom)).app
        (_root_.SheafOfModules.unit X.ringCatSheaf) = s := by
  rw [tensorSection_unit_eq, Category.assoc, (unitLeftIso F).hom_inv_id, Category.comp_id]

section Ext

variable [HasExt.{w} X.Modules]

/-- The actual tensor-extension wedge diagonal, now pulled back by the
actual natural tensor section, with no unit in its source object. -/
theorem tensorSectionExt_wedge_diagonal_eq_zero
    (F : X.Modules) (hF : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F)
    {A B : X.Modules} {n : ℕ} (ξ : Ext A B n)
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ F) :
    let := tensorRight_additive F
    let : PreservesFiniteLimits (tensorRight F) := (tensorRight_exact F hF).1
    let : PreservesFiniteColimits (tensorRight F) := (tensorRight_exact F hF).2
    ((Ext.mk₀ (C := X.Modules) ((tensorSection F s).app A)).comp
      (ξ.mapExactFunctor (tensorRight F)) (zero_add n)).comp
      (Ext.mk₀ (C := X.Modules) (tensorWedgeMap F s B)) (add_zero n) = 0 := by
  let := tensorRight_additive F
  let : PreservesFiniteLimits (tensorRight F) := (tensorRight_exact F hF).1
  let : PreservesFiniteColimits (tensorRight F) := (tensorRight_exact F hF).2
  have h := tensorExt_wedge_diagonal_eq_zero F hF ξ s
  change ((Ext.mk₀ (C := X.Modules) ((unitRightIso A).inv ≫
      (tensorBySection F s).app A)).comp
    (ξ.mapExactFunctor (tensorRight F)) (zero_add n)).comp
      (Ext.mk₀ (C := X.Modules) (tensorWedgeMap F s B)) (add_zero n) = 0
  rw [← Ext.mk₀_comp_mk₀,
    Ext.comp_assoc _ _ _ (zero_add 0) (zero_add n) (zero_add n),
    Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (zero_add n), h, Ext.comp_zero]

/-- The same formula uses the actual Yoneda class of the actual
tensorized short exact sequence, by native extClass functoriality. -/
theorem tensorSectionShortExact_wedge_diagonal_eq_zero
    (F : X.Modules) (hF : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F)
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ F) :
    let := tensorRight_additive F
    let : PreservesFiniteLimits (tensorRight F) := (tensorRight_exact F hF).1
    let : PreservesFiniteColimits (tensorRight F) := (tensorRight_exact F hF).2
    ((Ext.mk₀ (C := X.Modules) ((tensorSection F s).app S.X₃)).comp
      (hS.map_of_exact (tensorRight F)).extClass (zero_add 1)).comp
      (Ext.mk₀ (C := X.Modules) (tensorWedgeMap F s S.X₁)) (add_zero 1) = 0 := by
  let := tensorRight_additive F
  let : PreservesFiniteLimits (tensorRight F) := (tensorRight_exact F hF).1
  let : PreservesFiniteColimits (tensorRight F) := (tensorRight_exact F hF).2
  let p (e : Ext ((tensorRight F).obj S.X₃) ((tensorRight F).obj S.X₁) 1) :=
    ((Ext.mk₀ (C := X.Modules) ((tensorSection F s).app S.X₃)).comp e (zero_add 1)).comp
      (Ext.mk₀ (C := X.Modules) (tensorWedgeMap F s S.X₁)) (add_zero 1)
  exact (congrArg p (Ext.mapExactFunctor_extClass (tensorRight F) hS).symm).trans
    (tensorSectionExt_wedge_diagonal_eq_zero F hF hS.extClass s)

end Ext

end M9Native.MukaiTensorDiagonal
