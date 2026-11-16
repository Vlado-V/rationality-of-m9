module

public import M9StacksIntegration.MukaiWedgeDuality
public import M9StacksIntegration.MukaiHomAdjunction
public import M9StacksIntegration.MukaiTensorDiagonal
public import M9StacksIntegration.InvertibleExtCancellation

/-!
# Actual sections and coefficient wedge morphisms

Rank-two wedge duality and the actual linear tensor--Hom adjunction
identify genuine global sections with actual morphisms into the second
exterior power. Fully faithful tensoring by the actual line coefficient
then gives the morphisms consumed by native Hom--Serre duality.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace M9Native.MukaiSectionWedge

open M9Native.MukaiCupAlternating M9Native.MukaiHomExact
open M9Native.MukaiHomCoefficient M9Native.MukaiHomAdjunction
open M9Native.MukaiWedgeDuality M9Native.MukaiTensorSection M9Native.MukaiTensorDiagonal
open M9Native.InvertibleExtCancellation (unit)

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable {X : Scheme.{u}}

/-- Genuine sections of a rank-two bundle are actual wedge morphisms,
linearly and bijectively in the original scalar structure. -/
def sectionWedgeHomLinearEquiv (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) (C : X.Modules)
    (hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C 2) :
    letI := modulesLinearOverField k f
    (unit X ⟶ C) ≃ₗ[k] (C ⟶ exteriorSquare C) := by
  letI := modulesLinearOverField k f
  exact (Linear.homCongr k (Iso.refl (unit X))
      (rankTwoWedgeIso C hC)).trans
    ((tensorHomLinearEquiv k f C 2 hC (unit X)
      (exteriorSquare C)).symm.trans
        (Linear.homCongr k (unitLeftIso C) (Iso.refl (exteriorSquare C))))

/-- The actual bijection sends a section to wedge by that same section,
with its original order and sign. -/
theorem sectionWedgeHomLinearEquiv_apply (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) (C : X.Modules)
    (hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C 2)
    (s : unit X ⟶ C) :
    letI := modulesLinearOverField k f
    sectionWedgeHomLinearEquiv k f C hC s = wedgeBySection C (C.unitHomEquiv s) := by
  let := modulesLinearOverField k f
  let adj : tensorRight C ⊣ homFunctor C :=
    Stacks.SheafOfModules.InternalHom.sheafTensorRightHomAdjunction X.sheaf C
  let b := (adj.homEquiv (unit X)
    (exteriorSquare C)).symm (s ≫ (rankTwoWedgeIso C hC).hom)
  change (unitLeftIso C).inv ≫ b ≫ 𝟙 (exteriorSquare C) = _
  rw [Category.comp_id]
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext y
  rw [_root_.SheafOfModules.comp_val_app_apply]
  refine Eq.trans (congrArg (fun z => b.val.app U z)
    (Stacks.SheafOfModules.tensorSheafUnitLeftIso_inv_app X.sheaf.obj
      X.ringCatSheaf.property C U y)) ?_
  have h := transpose_on_local_tensor (unit X)
    C (exteriorSquare C) b U (1 : X.ringCatSheaf.obj.obj U) y
  have hb : adj.homEquiv (unit X) (exteriorSquare C) b =
      s ≫ (rankTwoWedgeIso C hC).hom := Equiv.apply_symm_apply _ _
  rw [hb] at h
  refine h.symm.trans ?_
  change Stacks.SheafOfModules.evalSection X.sheaf.obj C.val (exteriorSquare C).val U
    ((rankTwoWedgeIso C hC).hom.val.app U ((C.unitHomEquiv s).val U)) y = _
  exact rankTwoWedgeIso_eval C hC U ((C.unitHomEquiv s).val U) y

/-- An actual invertible coefficient and the actual determinant
identification give the actual transpose on global sections. -/
def twistedSectionWedgeHomLinearEquiv (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) (C N Ω : X.Modules)
    (hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C 2)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (d : tensor N (exteriorSquare C) ≅ Ω) :
    letI := modulesLinearOverField k f
    (unit X ⟶ C) ≃ₗ[k] (tensor N C ⟶ Ω) := by
  letI := modulesLinearOverField k f
  exact (sectionWedgeHomLinearEquiv k f C hC).trans
    ((tensorLeftHomLinearEquiv k f N C (exteriorSquare C)).trans
      (Linear.homCongr k (Iso.refl (tensor N C)) d))

/-- Its coefficient morphism is literally the checked tensor-wedge
morphism followed by the original determinant identification. -/
theorem twistedSectionWedgeHomLinearEquiv_apply (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) (C N Ω : X.Modules)
    (hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C 2)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (d : tensor N (exteriorSquare C) ≅ Ω)
    (s : unit X ⟶ C) :
    letI := modulesLinearOverField k f
    twistedSectionWedgeHomLinearEquiv k f C N Ω hC d s = tensorWedgeMap C s N ≫ d.hom := by
  let := modulesLinearOverField k f
  change 𝟙 (tensor N C) ≫
    tensorLeftHomLinearEquiv k f N C (exteriorSquare C)
      (sectionWedgeHomLinearEquiv k f C hC s) ≫ d.hom = _
  rw [Category.id_comp, sectionWedgeHomLinearEquiv_apply, tensorLeftHomLinearEquiv_apply]
  rfl

end M9Native.MukaiSectionWedge
