module

public import M9StacksIntegration.MukaiCupAlternating
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.FiniteLocallyFreeHomSection
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorHomAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction

/-!
# Exact native sheaf-Hom for a finite locally free module

The coefficient-variable tensor-dual comparison is proved natural on
local pure tensors. Its pointwise native isomorphisms therefore form an
actual natural isomorphism. Flatness of the genuine dual sheaf makes
native sheaf-Hom exact, allowing the actual tensor-Hom adjunction on Ext.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

universe u w

namespace M9Native.MukaiHomExact

open M9Native.MukaiCupAlternating

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

variable {X : Scheme.{u}}

/-- The native internal-Hom functor with its original module category. -/
abbrev homFunctor (F : X.Modules) : X.Modules ⥤ X.Modules :=
  Stacks.SheafOfModules.InternalHom.internalHomSecondFunctor.{u,u,u,u}
    (Opens.grothendieckTopology X) X.sheaf F

/-- Tensoring a coefficient morphism on a genuine local pure tensor. -/
theorem tensorRight_map_unit (D : X.Modules) {M N : X.Modules} (g : M ⟶ N)
    (U : X.Opensᵒᵖ) (m : M.val.obj U) (d : D.val.obj U) :
    ((tensorRight D).map g).val.app U
        ((PresheafOfModules.tensorSheafUnit M D).app U (m ⊗ₜ d)) =
      (PresheafOfModules.tensorSheafUnit N D).app U (g.val.app U m ⊗ₜ d) := by
  have h := Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
    X.sheaf M D g (𝟙 D) U m d
  have hid : ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj N).map (𝟙 D) =
      𝟙 _ := ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj N).map_id D
  rw [hid, Category.comp_id] at h
  exact h

/-- The native rank-one local morphism commutes with coefficient
postcomposition. -/
theorem rankOneHomSection_post (F : X.Modules) {M N : X.Modules} (g : M ⟶ N)
    (U : X.Opensᵒᵖ) (m : M.val.obj U)
    (l : (Stacks.SheafOfModules.dualSheaf X.sheaf.obj X.ringCatSheaf.property F).val.obj U) :
    ((homFunctor F).map g).val.app U
        (Stacks.SheafOfModules.rankOneHomSection X.sheaf.obj X.ringCatSheaf.property m l) =
      Stacks.SheafOfModules.rankOneHomSection X.sheaf.obj X.ringCatSheaf.property
        (g.val.app U m) l := by
  apply Stacks.SheafOfModules.internalHom_ext X.sheaf.obj X.ringCatSheaf.property
  intro V y
  change g.val.app (op V.unop.left)
      (Stacks.SheafOfModules.dualApp l V y • Stacks.SheafOfModules.resSection V m) =
    Stacks.SheafOfModules.dualApp l V y •
      Stacks.SheafOfModules.resSection V (g.val.app U m)
  rw [map_smul]
  congr 1
  exact PresheafOfModules.naturality_apply g.val V.unop.hom.op m

/-- Naturality of the actual tensor-dual comparison, proved without
postulating a comparison of the coefficient functors. -/
theorem tensorDualToSheafHom_naturality (F : X.Modules) {M N : X.Modules}
    (g : M ⟶ N) :
    (tensorRight (Stacks.SheafOfModules.dualSheaf X.sheaf.obj X.ringCatSheaf.property F)).map g ≫
        Stacks.SheafOfModules.tensorDualToSheafHom X.sheaf.obj X.ringCatSheaf.property F N =
      Stacks.SheafOfModules.tensorDualToSheafHom X.sheaf.obj X.ringCatSheaf.property F M ≫
        (homFunctor F).map g := by
  apply PresheafOfModules.tensorSheaf_hom_ext
  intro U m l
  rw [_root_.SheafOfModules.comp_val_app_apply,
    _root_.SheafOfModules.comp_val_app_apply]
  refine Eq.trans (congrArg
    (fun z => (Stacks.SheafOfModules.tensorDualToSheafHom X.sheaf.obj
      X.ringCatSheaf.property F N).val.app U z)
    (tensorRight_map_unit
      (Stacks.SheafOfModules.dualSheaf X.sheaf.obj X.ringCatSheaf.property F) g U m l)) ?_
  change (Stacks.SheafOfModules.tensorDualToSheafHom X.sheaf.obj X.ringCatSheaf.property F N).val.app U
      (Stacks.SheafOfModules.toTensorSheafSection X.sheaf.obj X.ringCatSheaf.property N
        (Stacks.SheafOfModules.dualSheaf X.sheaf.obj X.ringCatSheaf.property F) U
        (g.val.app U m ⊗ₜ l)) = _
  refine Eq.trans
    (Stacks.SheafOfModules.tensorDualToSheafHom_toTensorSheafSection
      X.sheaf.obj X.ringCatSheaf.property F N U (g.val.app U m) l) ?_
  change _ = ((homFunctor F).map g).val.app U
      ((Stacks.SheafOfModules.tensorDualToSheafHom X.sheaf.obj X.ringCatSheaf.property F M).val.app U
        (Stacks.SheafOfModules.toTensorSheafSection X.sheaf.obj X.ringCatSheaf.property M
          (Stacks.SheafOfModules.dualSheaf X.sheaf.obj X.ringCatSheaf.property F) U (m ⊗ₜ l)))
  exact (rankOneHomSection_post F g U m l).symm.trans
    (congrArg (fun z => ((homFunctor F).map g).val.app U z)
      (Stacks.SheafOfModules.tensorDualToSheafHom_toTensorSheafSection
        X.sheaf.obj X.ringCatSheaf.property F M U m l).symm)

/-- The actual native pointwise tensor-dual isomorphisms assemble
naturally, for the genuine finite locally free bundle. -/
def tensorDualHomNatIso (F : X.Modules) (r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r) :
    tensorRight (Stacks.SheafOfModules.dualSheaf X.sheaf.obj X.ringCatSheaf.property F) ≅
      homFunctor F := by
  letI := hF
  exact NatIso.ofComponents
    (fun M => Stacks.SheafOfModules.tensorDualIsoSheafHomOfRank F M r)
    (fun g => tensorDualToSheafHom_naturality F g)

/-- Native sheaf-Hom from a finite locally free bundle is exact because
it is naturally tensoring with the actual finite locally free dual. -/
theorem homFunctor_exact (F : X.Modules) (r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r) :
    exactFunctor X.Modules X.Modules (homFunctor F) := by
  let D := Stacks.SheafOfModules.dualSheaf X.sheaf.obj X.ringCatSheaf.property F
  let := hF
  have hD : SheafOfModules.IsFiniteLocallyFree.{u,u,u} D :=
    Stacks.AlgebraicGeometry.ReflexiveModules.isFiniteLocallyFree_dualSheaf F
      (SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F r)
  let : PreservesFiniteLimits (tensorRight D) := (tensorRight_exact D hD).1
  let : PreservesFiniteColimits (tensorRight D) := (tensorRight_exact D hD).2
  exact ⟨preservesFiniteLimits_of_natIso (tensorDualHomNatIso F r hF),
    preservesFiniteColimits_of_natIso (tensorDualHomNatIso F r hF)⟩

end M9Native.MukaiHomExact
