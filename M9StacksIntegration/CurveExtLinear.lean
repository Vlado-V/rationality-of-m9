module

public import M9StacksIntegration.InvertibleExtCancellation
public import M9StacksIntegration.UnitExtCohomologyNaturality
public import M9StacksIntegration.InvertibleHomCancellation
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Scalar-compatible Ext cancellation on the original curve modules

These are the actual native Yoneda Ext groups and the original
`modulesLinearOverField` scalar structure. The additive cancellation
maps retain their exact underlying functions; their linear upgrades
allow the cotangent deformation classifier to preserve field scalars.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open M9Native.InvertibleExtCancellation
open M9StacksIntegration.InvertibleHomCancellation

universe u v w

namespace M9Native.CurveExtLinear

section General

variable (R : Type*) [Ring R] {C : Type u} [Category.{v} C] [Abelian C]
  [HasExt.{w} C] [Linear R C] (F : C ⥤ C) [F.IsEquivalence] [F.Additive] [F.Linear R]

def exactEquivalenceExtLinearEquiv (A B : C) (n : ℕ) :
    Ext A B n ≃ₗ[R] Ext (F.obj A) (F.obj B) n := by
  apply LinearEquiv.ofBijective (F.mapExtLinearMap R A B n)
  have hf : (fun e : Ext A B n => (F.mapExtLinearMap R A B n) e) =
      exactEquivalenceExt F A B n := by
    funext e
    exact (exactEquivalenceExt_apply F A B n e).symm
  change Function.Bijective (fun e : Ext A B n => (F.mapExtLinearMap R A B n) e)
  rw [hf]
  exact (exactEquivalenceExt F A B n).bijective

end General

variable {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k))

local instance nativeHasExt : HasExt.{u} X.Modules := hasExt_of_enoughInjectives X.Modules

def tensorRightExtLinearEquiv (W : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property W]
    (A B : X.Modules) (n : ℕ) :
    letI := modulesLinearOverField k f
    Ext.{u} A B n ≃ₗ[k] Ext.{u} ((tensorRight W).obj A) ((tensorRight W).obj B) n := by
  let := modulesLinearOverField k f
  let := tensorRight_additive W
  let := tensorRight_linear f W
  let : (tensorRight W).IsEquivalence := Scheme.Modules.isEquivalence_invertibleTensorRightFunctor W
  exact exactEquivalenceExtLinearEquiv k (tensorRight W) A B n

theorem tensorRightExtLinearEquiv_toAddEquiv (W : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property W]
    (A B : X.Modules) (n : ℕ) :
    letI := modulesLinearOverField k f
    (tensorRightExtLinearEquiv f W A B n).toAddEquiv = tensorRightExtEquiv W A B n := by
  let := modulesLinearOverField k f
  let := tensorRight_additive W
  let : (tensorRight W).IsEquivalence := Scheme.Modules.isEquivalence_invertibleTensorRightFunctor W
  ext e
  exact (tensorRightExtEquiv_apply W A B n e).symm

def invertibleExtUnitLinearEquiv (L Q : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (n : ℕ) :
    letI := modulesLinearOverField k f
    Ext.{u} L Q n ≃ₗ[k] Ext.{u} (unit X)
      (Scheme.Modules.tensorObj Q (Scheme.Modules.tensorInverse L)) n := by
  let := modulesLinearOverField k f
  let : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Scheme.Modules.tensorInverse L) := Scheme.Modules.isInvertible_tensorInverse L
  refine { __ := invertibleExtUnitEquiv L Q n, map_smul' := ?_ }
  intro a e
  have ht : tensorRightExtEquiv (Scheme.Modules.tensorInverse L) L Q n (a • e) =
      a • tensorRightExtEquiv (Scheme.Modules.tensorInverse L) L Q n e := by
    rw [← tensorRightExtLinearEquiv_toAddEquiv f (Scheme.Modules.tensorInverse L) L Q n]
    exact (tensorRightExtLinearEquiv f (Scheme.Modules.tensorInverse L) L Q n).map_smul a e
  change (Ext.mk₀ (inverseTensorUnitIso L).inv).comp
      (tensorRightExtEquiv (Scheme.Modules.tensorInverse L) L Q n (a • e)) (zero_add n) =
    a • (Ext.mk₀ (inverseTensorUnitIso L).inv).comp
      (tensorRightExtEquiv (Scheme.Modules.tensorInverse L) L Q n e) (zero_add n)
  rw [ht, Ext.comp_smul]

theorem invertibleExtUnitLinearEquiv_toAddEquiv (L Q : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (n : ℕ) :
    letI := modulesLinearOverField k f
    (invertibleExtUnitLinearEquiv f L Q n).toAddEquiv = invertibleExtUnitEquiv L Q n := by
  let := modulesLinearOverField k f
  rfl

def invertibleExtOneCohomologyLinearEquiv (L Q : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    letI := modulesLinearOverField k f
    Ext.{u} L Q 1 ≃ₗ[k] cohomologyOverField k f
      (Scheme.Modules.tensorObj Q (Scheme.Modules.tensorInverse L)) 1 := by
  let := modulesLinearOverField k f
  exact (invertibleExtUnitLinearEquiv f L Q 1).trans
    (UnitExtCohomologyNaturality.unitExtCohomologyLinearEquiv k f _)

theorem invertibleExtOneCohomologyLinearEquiv_toAddEquiv (L Q : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    letI := modulesLinearOverField k f
    (invertibleExtOneCohomologyLinearEquiv f L Q).toAddEquiv =
      invertibleExtCohomologyAddEquiv k f L Q 1 := by
  let := modulesLinearOverField k f
  rfl

end M9Native.CurveExtLinear
