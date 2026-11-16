module

public import M9StacksIntegration.InvertibleExtCancellation
public import StacksFrontier.AlgebraicGeometry.Cohomology.ExtFromStructureSheafLinear

/-!
# Coefficient naturality of the native unit-Ext/cohomology comparison

The small enough-injectives `Ext.{u}` used by the native extension construction
is transported to the standard `Ext.{u+1}` before applying the actual Stacks
comparison.  The transport respects postcomposition.  Consequently the exact
additive comparison used in `InvertibleExtCancellation` is natural for the
actual `cohomologyOverFieldMap`.

The linear upgrade below uses the existing `modulesLinearOverField` action
directly, through `cohomologyOverFieldMap_smul`.  No identification with the
separate `Scheme.Modules.linearOverBase` instance is assumed.

The imported coefficient-naturality provider is
`StacksFrontier/AlgebraicGeometry/Cohomology/ExtFromStructureSheafLinear.lean`
at Stacks revision `c496df` (Apache-2.0).
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace M9Native.UnitExtCohomologyNaturality

open M9Native.InvertibleExtCancellation

variable {X : Scheme.{u}}

attribute [local instance] HasDerivedCategory.standard HasExt.standard

local instance nativeHasExt (X : Scheme.{u}) : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules

/-- Additive universe transport through the same standard derived model used
by the native comparison.  The unit has the explicit type `X.Modules`. -/
def unitExtUniverseAddEquiv (Q : X.Modules) (n : ℕ) :
    Ext.{u} (unit X) Q n ≃+ Ext.{u+1} (unit X) Q n :=
  Ext.homAddEquiv.{u+1,u,u,u+1}.trans
    Ext.homAddEquiv.{u+1,u+1,u,u+1}.symm

/-- The transport preserves the actual derived morphism. -/
@[simp]
theorem unitExtUniverseAddEquiv_hom (Q : X.Modules) (n : ℕ)
    (e : Ext.{u} (unit X) Q n) :
    (unitExtUniverseAddEquiv Q n e).hom = e.hom := by
  exact Ext.homAddEquiv.{u+1,u+1,u,u+1}.apply_symm_apply
    (Ext.homAddEquiv.{u+1,u,u,u+1} e)

/-- This additive transport is the model-independent change-of-universe map. -/
theorem unitExtUniverseAddEquiv_eq_chgUniv (Q : X.Modules) (n : ℕ)
    (e : Ext.{u} (unit X) Q n) :
    unitExtUniverseAddEquiv Q n e = Ext.chgUniv.{u+1} e := by
  apply Ext.homEquiv.{u+1,u+1,u,u+1}.injective
  exact (unitExtUniverseAddEquiv_hom Q n e).trans
    (Ext.homEquiv_chgUniv.{u+1,u+1,u,u,u+1} e).symm

/-- Universe transport commutes with coefficient postcomposition in every
degree, before the degree-one cohomology theorem is applied. -/
theorem unitExtUniverseAddEquiv_comp_mk₀ {Q R : X.Modules} (g : Q ⟶ R)
    (n : ℕ) (e : Ext.{u} (unit X) Q n) :
    unitExtUniverseAddEquiv R n (e.comp (Ext.mk₀ g) (add_zero n)) =
      (unitExtUniverseAddEquiv Q n e).comp (Ext.mk₀ g) (add_zero n) := by
  apply Ext.homEquiv.{u+1,u+1,u,u+1}.injective
  change (unitExtUniverseAddEquiv R n
    (e.comp (Ext.mk₀ g) (add_zero n))).hom = _
  simp only [unitExtUniverseAddEquiv_hom, Ext.comp_hom, Ext.mk₀_hom]

/-- The original small-Ext comparison is precisely the native standard-Ext
comparison after the actual universe transport. -/
theorem unitExtCohomologyAddEquiv_eq_standard (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) (Q : X.Modules) (n : ℕ)
    (e : Ext.{u} (unit X) Q n) :
    unitExtCohomologyAddEquiv k f Q n e =
      Stacks.Cohomology.SpaceModules.extEquivModuleCohomology X.ringCatSheaf Q n
        (unitExtUniverseAddEquiv Q n e) := rfl

/-- The exact small-Ext comparison used for invertible-sheaf cancellation is
natural in the coefficient sheaf, with the actual native `H¹` map. -/
theorem unitExtCohomologyAddEquiv_naturality_one (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) {Q R : X.Modules} (g : Q ⟶ R)
    (e : Ext.{u} (unit X) Q 1) :
    unitExtCohomologyAddEquiv k f R 1 (e.comp (Ext.mk₀ g) (add_zero 1)) =
      cohomologyOverFieldMap k f g 1 (unitExtCohomologyAddEquiv k f Q 1 e) := by
  rw [unitExtCohomologyAddEquiv_eq_standard,
    unitExtCohomologyAddEquiv_eq_standard, unitExtUniverseAddEquiv_comp_mk₀]
  unfold cohomologyOverFieldMap
  exact Stacks.Cohomology.SpaceModules.extEquivModuleCohomology_naturality_one
    X.ringCatSheaf Q R g (unitExtUniverseAddEquiv Q 1 e)

/-- Compatibility on underlying elements with the actual native linear
provider; its own scalar instance is explicitly retained here. -/
theorem unitExtCohomologyAddEquiv_eq_native_linear (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) (Q : X.Modules) (e : Ext.{u} (unit X) Q 1) :
    letI := Scheme.Modules.linearOverBase f
    unitExtCohomologyAddEquiv k f Q 1 e =
      extOneLinearEquivCohomologyOverField f Q (unitExtUniverseAddEquiv Q 1 e) := by
  let := Scheme.Modules.linearOverBase f
  rfl

/-- The same comparison, with the exact native `modulesLinearOverField`
structure used by the extension construction, is `k`-linear. -/
def unitExtCohomologyLinearEquiv (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) (Q : X.Modules) :
    letI := modulesLinearOverField k f
    Ext.{u} (unit X) Q 1 ≃ₗ[k] cohomologyOverField k f Q 1 := by
  letI := modulesLinearOverField k f
  refine { __ := unitExtCohomologyAddEquiv k f Q 1, map_smul' := ?_ }
  intro a e
  refine Eq.trans (congrArg (unitExtCohomologyAddEquiv k f Q 1)
    (Ext.smul_eq_comp_mk₀ e a)) ?_
  refine Eq.trans
    (unitExtCohomologyAddEquiv_naturality_one k f (a • 𝟙 Q) e) ?_
  rw [cohomologyOverFieldMap_smul, cohomologyOverFieldMap_id]
  rfl

/-- The linear upgrade retains the original additive comparison exactly. -/
theorem unitExtCohomologyLinearEquiv_toAddEquiv (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) (Q : X.Modules) :
    letI := modulesLinearOverField k f
    (unitExtCohomologyLinearEquiv k f Q).toAddEquiv =
      unitExtCohomologyAddEquiv k f Q 1 := by
  let := modulesLinearOverField k f
  ext e
  rfl

end M9Native.UnitExtCohomologyNaturality
