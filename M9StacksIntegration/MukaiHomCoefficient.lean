module

public import M9StacksIntegration.MukaiTensorSection
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAssociatorSections

/-!
# The actual tensor-coefficient comparison for native sheaf-Hom

Finite local freeness constructs the actual coefficient isomorphism
`N tensor Hom(F,D) = Hom(F,N tensor D)`. Its section evaluation is proved
from the native tensor-dual formula and associator on actual local pure
tensors. This is the sheaf identity needed before the checked Yoneda
diagonal can be passed through actual duality.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace M9Native.MukaiHomCoefficient

open M9Native.MukaiCupAlternating M9Native.MukaiHomExact
open M9Native.MukaiTensorSection M9Native.MukaiExtEvaluation

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable {X : Scheme.{u}}

/-- The original native tensor product, with no change of module model. -/
abbrev tensor (A B : X.Modules) : X.Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj A).obj B

/-- The actual image of a local pure tensor in the tensor sheaf. -/
abbrev pureTensor (A B : X.Modules) (U : X.Opensᵒᵖ)
    (a : A.val.obj U) (b : B.val.obj U) : (tensor A B).val.obj U :=
  (PresheafOfModules.tensorSheafUnit A B).app U (a ⊗ₜ b)

/-- The native explicit associator, typed in the original module category. -/
abbrev tensorAssociator (A B D : X.Modules) :
    tensor (tensor A B) D ≅ tensor A (tensor B D) :=
  Stacks.SheafOfModules.tensorSheafAssociator
    X.sheaf.obj X.ringCatSheaf.property A B D

/-- Coefficient morphisms act on actual pure tensors in the second factor. -/
theorem tensorLeft_map_pure (A : X.Modules) {B D : X.Modules} (g : B ⟶ D)
    (U : X.Opensᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj A).map g).val.app U
        (pureTensor A B U a b) = pureTensor A D U a (g.val.app U b) := by
  have h := Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
    X.sheaf A B (𝟙 A) g U a b
  have hi : ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map (𝟙 A)).app B =
      𝟙 _ := NatTrans.congr_app ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map_id A) B
  rw [hi, Category.id_comp] at h
  exact h

/-- The actual explicit associator rebrackets actual pure tensors. -/
theorem tensorAssociator_pure (A B D : X.Modules) (U : X.Opensᵒᵖ)
    (a : A.val.obj U) (b : B.val.obj U) (d : D.val.obj U) :
    (tensorAssociator A B D).hom.val.app U
        (pureTensor (tensor A B) D U (pureTensor A B U a b) d) =
      pureTensor A (tensor B D) U a (pureTensor B D U b d) :=
  Stacks.SheafOfModules.tensorSheafAssociator_hom_val_app_tmul
    X.sheaf.obj X.ringCatSheaf.property A B D U a b d

/-- The actual evaluation map induced by an actual global section. -/
abbrev evaluation (F : X.Modules)
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ F) (D : X.Modules) :
    (homFunctor F).obj D ⟶ D :=
  adjunctionEvaluation
    (Stacks.SheafOfModules.InternalHom.sheafTensorRightHomAdjunction X.sheaf F)
    (tensorSection F s) D

/-- On the actual native rank-one local morphism, section evaluation is
the original functional evaluated on the original section. -/
theorem evaluation_rankOne (F D : X.Modules)
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ F)
    (U : X.Opensᵒᵖ) (d : D.val.obj U)
    (l : (Stacks.SheafOfModules.dualSheaf X.sheaf.obj X.ringCatSheaf.property F).val.obj U) :
    (evaluation F s D).val.app U
        (Stacks.SheafOfModules.rankOneHomSection X.sheaf.obj X.ringCatSheaf.property d l) =
      Stacks.SheafOfModules.dualEval l ((F.unitHomEquiv s).val U) • d := by
  refine Eq.trans (adjunctionEvaluation_app F D s U _) ?_
  exact (Stacks.SheafOfModules.rankOneHomSection_app X.sheaf.obj X.ringCatSheaf.property
    d l (op (Over.mk (𝟙 U.unop))) ((F.unitHomEquiv s).val U)).trans (by
      rw [Stacks.SheafOfModules.dualApp_self, Stacks.SheafOfModules.resSection_self])

/-- The actual tensor-coefficient isomorphism of native sheaf-Hom,
constructed from genuine native tensor-dual and associator isomorphisms. -/
def homCoefficientIso (F : X.Modules) (r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r) (N D : X.Modules) :
    tensor N ((homFunctor F).obj D) ≅ (homFunctor F).obj (tensor N D) :=
  ((tensorAssociator N D
      (Stacks.SheafOfModules.dualSheaf X.sheaf.obj X.ringCatSheaf.property F)) ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj N).mapIso
      ((tensorDualHomNatIso F r hF).app D)).symm ≪≫
    (tensorDualHomNatIso F r hF).app (tensor N D)

/-- The genuine coefficient isomorphism commutes with literal section
evaluation. The equality is proved on actual triple pure tensors, using
the native rank-one and associator formulas. -/
theorem homCoefficientIso_evaluation (F : X.Modules) (r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r) (N D : X.Modules)
    (s : _root_.SheafOfModules.unit X.ringCatSheaf ⟶ F) :
    (homCoefficientIso F r hF N D).hom ≫ evaluation F s (tensor N D) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj N).map (evaluation F s D) := by
  let V := Stacks.SheafOfModules.dualSheaf X.sheaf.obj X.ringCatSheaf.property F
  let θ := tensorDualHomNatIso F r hF
  let p : tensor (tensor N D) V ≅ tensor N ((homFunctor F).obj D) :=
    tensorAssociator N D V ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj N).mapIso (θ.app D)
  have h : (θ.app (tensor N D)).hom ≫ evaluation F s (tensor N D) =
      p.hom ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj N).map (evaluation F s D) := by
    apply PresheafOfModules.tensorSheaf_hom_ext₂
      (Osharp := X.sheaf) (F := N) (G := D) (H := V) (Q := tensor N D)
    intro U n d l
    let z := pureTensor (tensor N D) V U (pureTensor N D U n d) l
    let rd := Stacks.SheafOfModules.rankOneHomSection X.sheaf.obj X.ringCatSheaf.property d l
    have hθD : (θ.app D).hom.val.app U (pureTensor D V U d l) = rd :=
      Stacks.SheafOfModules.tensorDualToSheafHom_toTensorSheafSection
        X.sheaf.obj X.ringCatSheaf.property F D U d l
    have hθND : (θ.app (tensor N D)).hom.val.app U z =
        Stacks.SheafOfModules.rankOneHomSection X.sheaf.obj X.ringCatSheaf.property
          (pureTensor N D U n d) l :=
      Stacks.SheafOfModules.tensorDualToSheafHom_toTensorSheafSection
        X.sheaf.obj X.ringCatSheaf.property F (tensor N D) U (pureTensor N D U n d) l
    have hp : p.hom.val.app U z = pureTensor N ((homFunctor F).obj D) U n rd := by
      change ((tensorAssociator N D V).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj N).map (θ.app D).hom).val.app U z = _
      rw [_root_.SheafOfModules.comp_val_app_apply]
      refine Eq.trans (congrArg (fun t =>
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj N).map (θ.app D).hom).val.app U t)
          (tensorAssociator_pure N D V U n d l)) ?_
      exact (tensorLeft_map_pure N (θ.app D).hom U n (pureTensor D V U d l)).trans
        (congrArg (pureTensor N ((homFunctor F).obj D) U n) hθD)
    have hsmul : pureTensor N D U n
          (Stacks.SheafOfModules.dualEval l ((F.unitHomEquiv s).val U) • d) =
        Stacks.SheafOfModules.dualEval l ((F.unitHomEquiv s).val U) • pureTensor N D U n d := by
      let : CommRing (X.ringCatSheaf.obj.obj U) :=
        inferInstanceAs (CommRing (X.sheaf.obj.obj U))
      let a : X.ringCatSheaf.obj.obj U :=
        Stacks.SheafOfModules.dualEval l ((F.unitHomEquiv s).val U)
      change (PresheafOfModules.tensorSheafUnit N D).app U
        (n ⊗ₜ[X.ringCatSheaf.obj.obj U] (a • d)) =
          a • (PresheafOfModules.tensorSheafUnit N D).app U
            (n ⊗ₜ[X.ringCatSheaf.obj.obj U] d)
      rw [TensorProduct.tmul_smul (R := X.ringCatSheaf.obj.obj U)]
      exact ((PresheafOfModules.tensorSheafUnit N D).app U).hom.map_smul _ _
    change ((θ.app (tensor N D)).hom ≫ evaluation F s (tensor N D)).val.app U z =
      (p.hom ≫ ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj N).map
        (evaluation F s D)).val.app U z
    rw [_root_.SheafOfModules.comp_val_app_apply,
      _root_.SheafOfModules.comp_val_app_apply]
    refine Eq.trans (congrArg (fun t => (evaluation F s (tensor N D)).val.app U t) hθND) ?_
    refine Eq.trans (evaluation_rankOne F (tensor N D) s U (pureTensor N D U n d) l) ?_
    refine Eq.trans hsmul.symm ?_
    refine Eq.trans (congrArg (pureTensor N D U n) (evaluation_rankOne F D s U d l).symm) ?_
    refine Eq.trans (tensorLeft_map_pure N (evaluation F s D) U n rd).symm ?_
    exact congrArg (fun t =>
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj N).map
        (evaluation F s D)).val.app U t) hp.symm
  have hpi : p.hom ≫ (homCoefficientIso F r hF N D).hom =
      (θ.app (tensor N D)).hom := by
    change p.hom ≫ (p.inv ≫ (θ.app (tensor N D)).hom) = _
    exact p.hom_inv_id_assoc _
  apply (cancel_epi p.hom).mp
  rw [← Category.assoc, hpi]
  exact h

end M9Native.MukaiHomCoefficient
