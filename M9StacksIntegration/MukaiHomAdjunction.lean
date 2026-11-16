module

public import M9StacksIntegration.MukaiHomCoefficient
public import M9StacksIntegration.MukaiTensorSection
public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafBraidingSections

/-!
# Actual linear tensor--Hom and invertible tensoring on morphisms

The maps retain the original `modulesLinearOverField` scalar action.
Their explicit formulas will identify the actual wedge section with its
actual coefficient morphism in the native Hom--Serre pairing.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace M9Native.MukaiHomAdjunction

open M9Native.MukaiCupAlternating M9Native.MukaiHomExact
open M9Native.MukaiExtAdjunction M9Native.MukaiHomCoefficient

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable {X : Scheme.{u}}

/-- The genuine tensor--Hom hom-equivalence, linear for the exact
original scalar structure. -/
def tensorHomLinearEquiv (k : Type u) [Field k] (f : X ⟶ Spec (.of k))
    (C : X.Modules) (r : ℕ)
    (hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C r)
    (A D : X.Modules) :
    letI := modulesLinearOverField k f
    ((tensorRight C).obj A ⟶ D) ≃ₗ[k] (A ⟶ (homFunctor C).obj D) := by
  letI := modulesLinearOverField k f
  letI := tensorRight_additive C
  letI := homFunctor_linear k f C r hC
  let adj : tensorRight C ⊣ homFunctor C :=
    Stacks.SheafOfModules.InternalHom.sheafTensorRightHomAdjunction X.sheaf C
  refine { __ := adj.homAddEquiv A D, map_smul' := ?_ }
  intro a g
  change adj.homEquiv A D (a • g) = a • adj.homEquiv A D g
  rw [adj.homEquiv_unit, adj.homEquiv_unit, Functor.map_smul, Linear.comp_smul]

/-- Its inverse is the actual native adjunction inverse, rather than an
independently chosen bijection on the same spaces. -/
theorem tensorHomLinearEquiv_symm_apply (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) (C : X.Modules) (r : ℕ)
    (hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C r)
    (A D : X.Modules) (g : A ⟶ (homFunctor C).obj D) :
    letI := modulesLinearOverField k f
    (tensorHomLinearEquiv k f C r hC A D).symm g =
      ((Stacks.SheafOfModules.InternalHom.sheafTensorRightHomAdjunction X.sheaf C).homEquiv
        A D).symm g := by
  let := modulesLinearOverField k f
  rfl

/-- The actual sheafified tensor symmetry. -/
abbrev tensorSwap (A D : X.Modules) : tensor A D ≅ tensor D A :=
  Stacks.SheafOfModules.Invertible.tensorProductBraiding X.sheaf.obj
    X.ringCatSheaf.property A D

/-- The actual symmetry exchanges the two original local pure factors. -/
theorem tensorSwap_pure (A D : X.Modules) (U : X.Opensᵒᵖ)
    (a : A.val.obj U) (d : D.val.obj U) :
    (tensorSwap A D).hom.val.app U (pureTensor A D U a d) =
      pureTensor D A U d a :=
  Stacks.SheafOfModules.tensorSections_braidingAt X.sheaf.obj
    X.ringCatSheaf.property U A D a d

/-- Tensoring by an actual invertible left factor is a genuine linear
bijection on morphisms, derived from fully faithful right tensoring. -/
def tensorLeftHomLinearEquiv (k : Type u) [Field k] (f : X ⟶ Spec (.of k))
    (N A D : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] :
    letI := modulesLinearOverField k f
    (A ⟶ D) ≃ₗ[k] (tensor N A ⟶ tensor N D) := by
  letI := modulesLinearOverField k f
  exact (M9StacksIntegration.InvertibleHomCancellation.tensorRightHomLinearEquiv f N A D).trans
    (Linear.homCongr k (tensorSwap N A).symm (tensorSwap D N))

/-- This bijection is literally the original left tensor functor on
morphisms; the equality is verified on actual local pure tensors. -/
theorem tensorLeftHomLinearEquiv_apply (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) (N A D : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (g : A ⟶ D) :
    letI := modulesLinearOverField k f
    tensorLeftHomLinearEquiv k f N A D g =
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj N).map g := by
  let := modulesLinearOverField k f
  change (tensorSwap N A).hom ≫ (tensorRight N).map g ≫
      (tensorSwap D N).hom = _
  apply PresheafOfModules.tensorSheaf_hom_ext
  intro U n a
  rw [_root_.SheafOfModules.comp_val_app_apply,
    _root_.SheafOfModules.comp_val_app_apply]
  refine Eq.trans (congrArg (fun z => (tensorSwap D N).hom.val.app U
    (((tensorRight N).map g).val.app U z)) (tensorSwap_pure N A U n a)) ?_
  refine Eq.trans (congrArg (fun z => (tensorSwap D N).hom.val.app U z)
    (tensorRight_map_unit N g U a n)) ?_
  exact (tensorSwap_pure D N U (g.val.app U a) n).trans
    (tensorLeft_map_pure N g U n a).symm

end M9Native.MukaiHomAdjunction
