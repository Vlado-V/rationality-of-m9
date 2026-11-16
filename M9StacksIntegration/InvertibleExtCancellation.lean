module

public import M9StacksIntegration.InvertibleHomCancellation
public import StacksFrontier.AlgebraicGeometry.Cohomology.ExtFromStructureSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Actual Ext cancellation by an invertible sheaf

Tensoring is the original native sheaf tensor functor. Its equivalence
therefore transports actual extension classes, rather than introducing a
replacement Ext group. The structure-sheaf comparison then reads these
classes as the native derived cohomology groups.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u v w

namespace M9Native.InvertibleExtCancellation

section ExactEquivalence

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  (F : C ⥤ C) [F.IsEquivalence] [F.Additive]

/-- The actual exact equivalence induces an additive equivalence on Ext. -/
def exactEquivalenceExt (A B : C) (n : ℕ) :
    Ext A B n ≃+ Ext (F.obj A) (F.obj B) n := by
  let E := F.asEquivalence
  letI : E.functor.Additive := inferInstanceAs F.Additive
  let e := ((extFunctorObj A n).mapIso (E.unitIso.app B)).addCommGroupIsoToAddEquiv
  exact e.trans E.toAdjunction.extEquiv.symm

/-- This is precisely the native map of extension classes. -/
theorem exactEquivalenceExt_apply (A B : C) (n : ℕ) (ξ : Ext A B n) :
    exactEquivalenceExt F A B n ξ = ξ.mapExactFunctor F := by
  let E := F.asEquivalence
  let : E.functor.Additive := inferInstanceAs F.Additive
  apply E.toAdjunction.extEquiv.injective
  change E.toAdjunction.extEquiv (E.toAdjunction.extEquiv.symm
    (((extFunctorObj A n).mapIso (E.unitIso.app B)).addCommGroupIsoToAddEquiv ξ)) = _
  rw [AddEquiv.apply_symm_apply]
  change ((extFunctorObj A n).mapIso (E.unitIso.app B)).hom ξ = _
  change ξ.comp (Ext.mk₀ (E.unitIso.app B).hom) (add_zero n) = _
  rw [Adjunction.extEquiv_apply]
  change ξ.comp (Ext.mk₀ (E.unitIso.hom.app B)) (add_zero n) =
    (Ext.mk₀ (E.unitIso.hom.app A)).comp
      ((ξ.mapExactFunctor E.functor).mapExactFunctor E.inverse) (zero_add n)
  simpa only [Ext.id_mapExactFunctor, Ext.comp_mapExactFunctor] using
    Ext.mapExactFunctor_comp_mk₀_natTransApp ξ E.unitIso.hom

theorem exactEquivalenceExt_comp {A B D : C} {a b c : ℕ}
    (ξ : Ext A B a) (η : Ext B D b) (h : a+b=c) :
    exactEquivalenceExt F A D c (ξ.comp η h) =
      (exactEquivalenceExt F A B a ξ).comp (exactEquivalenceExt F B D b η) h := by
  simp only [exactEquivalenceExt_apply, Ext.mapExactFunctor_comp]

theorem exactEquivalenceExt_mk₀ {A B : C} (g : A ⟶ B) :
    exactEquivalenceExt F A B 0 (Ext.mk₀ g) = Ext.mk₀ (F.map g) := by
  rw [exactEquivalenceExt_apply, Ext.mapExactFunctor_mk₀]

end ExactEquivalence

variable {X : Scheme.{u}}

/-- The unit with its category fixed to the native scheme module category. -/
abbrev unit (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

local instance nativeHasExt (X : Scheme.{u}) : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules

open M9StacksIntegration.InvertibleHomCancellation

/-- Tensoring by an actual invertible sheaf, on the actual native Ext groups. -/
def tensorRightExtEquiv (W : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property W]
    (A B : X.Modules) (n : ℕ) :
    Ext.{u} A B n ≃+ Ext.{u} ((tensorRight W).obj A) ((tensorRight W).obj B) n := by
  letI := tensorRight_additive W
  letI : (tensorRight W).IsEquivalence :=
    Scheme.Modules.isEquivalence_invertibleTensorRightFunctor W
  exact exactEquivalenceExt (tensorRight W) A B n

theorem tensorRightExtEquiv_apply (W : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property W]
    (A B : X.Modules) (n : ℕ) (ξ : Ext.{u} A B n) :
    letI := tensorRight_additive W
    letI : (tensorRight W).IsEquivalence :=
      Scheme.Modules.isEquivalence_invertibleTensorRightFunctor W
    tensorRightExtEquiv W A B n ξ = ξ.mapExactFunctor (tensorRight W) := by
  let := tensorRight_additive W
  let : (tensorRight W).IsEquivalence :=
    Scheme.Modules.isEquivalence_invertibleTensorRightFunctor W
  exact exactEquivalenceExt_apply (tensorRight W) A B n ξ

/-- The original invertible sheaf times its actual inverse tensor power. -/
def inverseTensorUnitIso (L : X.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible
      X.sheaf.obj X.ringCatSheaf.property L] :
    Scheme.Modules.tensorObj L (Scheme.Modules.tensorInverse L) ≅
      unit X := by
  letI : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL
  exact Stacks.SheafOfModules.Invertible.tensorProductIso X.sheaf.obj
      X.ringCatSheaf.property
      (Stacks.SheafOfModules.Invertible.tensorPowerOneIso X.sheaf.obj
        X.ringCatSheaf.property L).symm (Iso.refl _) ≪≫
    Stacks.SheafOfModules.TensorPower.tensorPowerMulIso X.sheaf.obj
      X.ringCatSheaf.property L 1 (-1)

/-- Ext from a line bundle is actual Ext from the structure sheaf after
the actual inverse tensor twist. -/
def invertibleExtUnitEquiv (L Q : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (n : ℕ) :
    Ext.{u} L Q n ≃+ Ext.{u} (unit X)
      (Scheme.Modules.tensorObj Q (Scheme.Modules.tensorInverse L)) n := by
  letI := Scheme.Modules.isInvertible_tensorInverse L
  let t := tensorRightExtEquiv (Scheme.Modules.tensorInverse L) L Q n
  let e := (((extFunctor n).mapIso (inverseTensorUnitIso L).symm.op).app
    (Scheme.Modules.tensorObj Q (Scheme.Modules.tensorInverse L))).addCommGroupIsoToAddEquiv
  exact t.trans e

/-- The native structure-sheaf Ext group, in the small enough-injectives
model used by the extension construction, computes the original derived
cohomology group over the original base field. -/
def unitExtCohomologyAddEquiv (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) (Q : X.Modules) (n : ℕ) :
    Ext.{u} (unit X) Q n ≃+
      cohomologyOverField k f Q n := by
  letI : HasDerivedCategory.{u+1} X.Modules := HasDerivedCategory.standard X.Modules
  exact Ext.homAddEquiv.{u+1,u,u,u+1}.trans
    (derivedHomStructureSheafEquivCohomologyOverField k f Q n)

/-- The actual Ext/cohomology identification needed by Mukai's
extension construction. No comparison is supplied as a hypothesis. -/
def invertibleExtCohomologyAddEquiv (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) (L Q : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (n : ℕ) :
    Ext.{u} L Q n ≃+
      cohomologyOverField k f
        (Scheme.Modules.tensorObj Q (Scheme.Modules.tensorInverse L)) n :=
  (invertibleExtUnitEquiv L Q n).trans (unitExtCohomologyAddEquiv k f _ n)

end M9Native.InvertibleExtCancellation
