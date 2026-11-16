module

public import M9StacksIntegration.UnitExtCohomologyNaturality

/-!
# All-degree naturality of the original unit-Ext/cohomology comparison

The maps here use the actual native delta-functor comparison and the original
modulesLinearOverField scalar action. Degree zero is normalized only by its
own image of the identity section; no identification of independently chosen
boundary comparisons is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Abelian Opposite AlgebraicGeometry
open TopologicalSpace
universe u

namespace M9Native.UnitExtCohomologyAllDegrees

section Site
attribute [local instance] HasDerivedCategory.standard HasExt.standard
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

private theorem site_apply (M : SheafOfModules.{u} R) (n : ℕ)
    (e : Ext (SheafOfModules.unit R) M n) :
    Stacks.Cohomology.SiteModules.extEquivCohomology R M n e =
      (eqToHom (Stacks.Cohomology.SiteModules.universalCohomologyDeltaFunctor_functor R n)).app M
        (AddEquiv.ulift.{u,u+1}
          (((Stacks.Cohomology.SiteModules.extCohomologyDeltaIso R).hom.app n).app M e)) := rfl

/-- Coefficient naturality in every degree, at the actual small site. -/
theorem site_naturality {M N : SheafOfModules.{u} R} (g : M ⟶ N)
    (n : ℕ) (e : Ext (SheafOfModules.unit R) M n) :
    Stacks.Cohomology.SiteModules.extEquivCohomology R N n
      (e.comp (Ext.mk₀ g) (add_zero n)) =
      (Stacks.Cohomology.SiteModules.cohomologyFunctor R n).map g
        (Stacks.Cohomology.SiteModules.extEquivCohomology R M n e) := by
  have hnat := congrArg (fun φ => AddEquiv.ulift.{u,u+1} (φ e))
    (((Stacks.Cohomology.SiteModules.extCohomologyDeltaIso R).hom.app n).naturality g)
  rw [site_apply, site_apply]
  erw [hnat]
  exact ConcreteCategory.congr_hom
    ((eqToHom (Stacks.Cohomology.SiteModules.universalCohomologyDeltaFunctor_functor R n)).naturality g) _
end Site

section Space
attribute [local instance] HasDerivedCategory.standard HasExt.standard
variable {Y : Type u} [TopologicalSpace Y]
  (R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u})

/-- Naturality for the native ringed-space abelian-group cohomology. -/
theorem space_naturality (M N : SheafOfModules.{u} R) (g : M ⟶ N)
    (n : ℕ) (e : Ext (SheafOfModules.unit R) M n) :
    Stacks.Cohomology.SpaceModules.extEquivCohomology R N n
      (e.comp (Ext.mk₀ g) (add_zero n)) =
      (Hfunctor R ⊤ n).map g
        (Stacks.Cohomology.SpaceModules.extEquivCohomology R M n e) := by
  have h1 := site_naturality R g n e
  have h2 := NatTrans.naturality_apply
    (Stacks.Cohomology.SpaceModules.cohomologyIsoSiteCohomology R n).hom g
    (Stacks.Cohomology.SiteModules.extEquivCohomology R M n e)
  dsimp [Stacks.Cohomology.SpaceModules.extEquivCohomology]
  rw [h1]
  exact h2

/-- Naturality for the actual right-derived module-valued sections. -/
theorem module_naturality (M N : SheafOfModules.{u} R) (g : M ⟶ N)
    (n : ℕ) (e : Ext (SheafOfModules.unit R) M n) :
    Stacks.Cohomology.SpaceModules.extEquivModuleCohomology R N n
      (e.comp (Ext.mk₀ g) (add_zero n)) =
      ((SheafOfModules.evaluation R (op (⊤ : TopologicalSpace.Opens Y))).rightDerived n).map g
        (Stacks.Cohomology.SpaceModules.extEquivModuleCohomology R M n e) := by
  have h1 := space_naturality R M N g n e
  have h2 := NatTrans.naturality_apply
    (Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso R ⊤ n).inv g
    (Stacks.Cohomology.SpaceModules.extEquivCohomology R M n e)
  dsimp [Stacks.Cohomology.SpaceModules.extEquivModuleCohomology]
  rw [h1]
  exact h2
end Space

section Scheme
attribute [local instance] HasDerivedCategory.standard HasExt.standard
open M9Native.InvertibleExtCancellation M9Native.UnitExtCohomologyNaturality
variable {X : Scheme.{u}}
local instance nativeHasExt (X : Scheme.{u}) : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules

/-- The original small-Ext additive comparison is coefficient-natural in all degrees. -/
theorem unitExtCohomologyAddEquiv_naturality (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) {Q T : X.Modules} (g : Q ⟶ T)
    (n : ℕ) (e : Ext.{u} (unit X) Q n) :
    unitExtCohomologyAddEquiv k f T n (e.comp (Ext.mk₀ g) (add_zero n)) =
      cohomologyOverFieldMap k f g n (unitExtCohomologyAddEquiv k f Q n e) := by
  rw [unitExtCohomologyAddEquiv_eq_standard,
    unitExtCohomologyAddEquiv_eq_standard, unitExtUniverseAddEquiv_comp_mk₀]
  unfold cohomologyOverFieldMap
  exact module_naturality X.ringCatSheaf Q T g n (unitExtUniverseAddEquiv Q n e)

/-- All degrees, with the exact original base-field scalar action. -/
def unitExtCohomologyLinearEquivAll (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) (Q : X.Modules) (n : ℕ) :
    letI := modulesLinearOverField k f
    Ext.{u} (unit X) Q n ≃ₗ[k] cohomologyOverField k f Q n := by
  letI := modulesLinearOverField k f
  refine { __ := unitExtCohomologyAddEquiv k f Q n, map_smul' := ?_ }
  intro a e
  refine Eq.trans (congrArg (unitExtCohomologyAddEquiv k f Q n)
    (Ext.smul_eq_comp_mk₀ e a)) ?_
  refine Eq.trans (unitExtCohomologyAddEquiv_naturality k f (a • 𝟙 Q) n e) ?_
  rw [cohomologyOverFieldMap_smul, cohomologyOverFieldMap_id]
  rfl

/-- Degree-zero Hom comparison obtained from the same all-degree delta isomorphism. -/
def unitHomCohomologyLinearEquivZero (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) (Q : X.Modules) :
    letI := modulesLinearOverField k f
    (unit X ⟶ Q) ≃ₗ[k] cohomologyOverField k f Q 0 := by
  letI := modulesLinearOverField k f
  exact (Ext.linearEquiv₀ (R := k)).symm.trans (unitExtCohomologyLinearEquivAll k f Q 0)

/-- The normalization vector is the actual image of the identity morphism. -/
def kappa (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) :
    cohomologyOverField k f (unit X) 0 :=
  unitExtCohomologyAddEquiv k f (unit X) 0 (Ext.mk₀ (𝟙 (unit X)))

/-- Naturality determines degree-zero comparison by evaluation on that single vector. -/
theorem unitHomCohomologyLinearEquivZero_apply (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) {Q : X.Modules} (s : unit X ⟶ Q) :
    letI := modulesLinearOverField k f
    unitHomCohomologyLinearEquivZero k f Q s =
      cohomologyOverFieldMap k f s 0 (kappa k f) := by
  let := modulesLinearOverField k f
  have h := unitExtCohomologyAddEquiv_naturality k f s 0 (Ext.mk₀ (𝟙 (unit X)))
  change unitExtCohomologyAddEquiv k f Q 0
    ((Ext.linearEquiv₀ (R := k)).symm s) = _
  rw [Ext.linearEquiv₀_symm_apply]
  simpa only [Ext.mk₀_comp_mk₀, Category.id_comp, kappa] using h
end Scheme
end M9Native.UnitExtCohomologyAllDegrees
