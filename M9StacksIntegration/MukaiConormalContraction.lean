module

public import M9StacksIntegration.MukaiTwistedSelfDualObstruction
public import M9StacksIntegration.MukaiHomAdjunction

/-!
# Actual contraction of a tensor-valued line

The map from an actual tensor line to `E ⊗ E` produces its actual
contraction `ξ ⊗ E∨ ⟶ E`. The formula on local decomposable tensors is
derived from the canonical double-dual map and native tensor--Hom
adjunction. No isomorphism, nondegeneracy, or line is constructed by an
assumption in this helper: the line-map is the input to this universal
construction, to be supplied later by the actual conormal kernel.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiHomExact M9Native.MukaiHomCoefficient M9Native.MukaiTensorSection
open scoped TensorProduct

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

namespace M9Native.MukaiConormalContraction

variable {X : Scheme.{u}}

/-- The canonical actual tensor-to-Hom map uses the actual double dual,
and so exists without a choice of a bundle basis or trivialization. -/
def tensorToHom (E : X.Modules) : tensor E E ⟶ (homFunctor (dualSheaf E)).obj E :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj E).map (toDoubleDual E) ≫
    Stacks.SheafOfModules.tensorDualToSheafHom X.sheaf.obj X.ringCatSheaf.property
      (dualSheaf E) E

theorem tensorToHom_pure (E : X.Modules) (U : X.Opensᵒᵖ)
    (e v : E.val.obj U) :
    (tensorToHom E).val.app U (pureTensor E E U e v) =
      Stacks.SheafOfModules.rankOneHomSection X.sheaf.obj X.ringCatSheaf.property e
        ((toDoubleDual E).val.app U v) := by
  rw [tensorToHom, _root_.SheafOfModules.comp_val_app_apply]
  refine (congrArg (fun z =>
      (Stacks.SheafOfModules.tensorDualToSheafHom X.sheaf.obj X.ringCatSheaf.property
        (dualSheaf E) E).val.app U z)
    (tensorLeft_map_pure E (toDoubleDual E) U e v)).trans ?_
  exact Stacks.SheafOfModules.tensorDualToSheafHom_toTensorSheafSection
    X.sheaf.obj X.ringCatSheaf.property (dualSheaf E) E U e _

/-- The actual line contraction, from native tensor--Hom adjunction. -/
def contraction {ξ E : X.Modules} (s : ξ ⟶ tensor E E) :
    M9Native.MukaiTwistedSelfDualObstruction.twistedDual ξ E ⟶ E :=
  ((Stacks.SheafOfModules.InternalHom.sheafTensorRightHomAdjunction
    X.sheaf (dualSheaf E)).homEquiv ξ E).symm (s ≫ tensorToHom E)

/-- The curry of the actual contraction is the original actual line map
followed by canonical tensor-to-Hom. -/
theorem contraction_curry {ξ E : X.Modules} (s : ξ ⟶ tensor E E) :
    (Stacks.SheafOfModules.InternalHom.sheafTensorRightHomAdjunction
      X.sheaf (dualSheaf E)).homEquiv ξ E (contraction s) = s ≫ tensorToHom E :=
  Equiv.apply_symm_apply _ _

/-- Its local values are literal local evaluation, before any basis or
determinant coordinates are introduced. -/
theorem contraction_local {ξ E : X.Modules} (s : ξ ⟶ tensor E E)
    (U : X.Opensᵒᵖ) (l : ξ.val.obj U) (φ : (dualSheaf E).val.obj U) :
    (contraction s).val.app U (pureTensor ξ (dualSheaf E) U l φ) =
      Stacks.SheafOfModules.evalSection X.sheaf.obj (dualSheaf E).val E.val U
        ((tensorToHom E).val.app U (s.val.app U l)) φ := by
  have h := transpose_on_local_tensor ξ (dualSheaf E) E (contraction s) U l φ
  rw [contraction_curry, _root_.SheafOfModules.comp_val_app_apply] at h
  exact h.symm

/-- For a decomposable local tensor the actual contraction is exactly
`l ⊗ φ ↦ φ(v) • e`, with no arbitrary scalar normalization. -/
theorem contraction_decomposable {ξ E : X.Modules} (s : ξ ⟶ tensor E E)
    (U : X.Opensᵒᵖ) (l : ξ.val.obj U) (φ : (dualSheaf E).val.obj U)
    (e v : E.val.obj U) (hs : s.val.app U l = pureTensor E E U e v) :
    (contraction s).val.app U (pureTensor ξ (dualSheaf E) U l φ) =
      Stacks.SheafOfModules.dualEval φ v • e := by
  rw [contraction_local, hs, tensorToHom_pure]
  have hd : Stacks.SheafOfModules.dualEval ((toDoubleDual E).val.app U v) φ =
      Stacks.SheafOfModules.dualEval φ v :=
    toDoubleDual_val_app_apply E U.unop v φ
  refine (Stacks.SheafOfModules.rankOneHomSection_app X.sheaf.obj X.ringCatSheaf.property
    e ((toDoubleDual E).val.app U v) (op (Over.mk (𝟙 U.unop))) φ).trans ?_
  rw [Stacks.SheafOfModules.dualApp_self, Stacks.SheafOfModules.resSection_self, hd]

/-- The contraction is attached naturally to the ACTUAL tensor line
map, including a change of the line itself. -/
theorem contraction_precomp {ξ η E : X.Modules} (s : ξ ⟶ tensor E E) (a : η ⟶ ξ) :
    contraction (a ≫ s) =
      ((M9Native.MukaiCupAlternating.tensorRight (dualSheaf E)).map a) ≫ contraction s := by
  apply ((Stacks.SheafOfModules.InternalHom.sheafTensorRightHomAdjunction
    X.sheaf (dualSheaf E)).homEquiv η E).injective
  rw [contraction_curry]
  rw [CategoryTheory.Adjunction.homEquiv_naturality_left]
  rw [contraction_curry, Category.assoc]

end M9Native.MukaiConormalContraction
