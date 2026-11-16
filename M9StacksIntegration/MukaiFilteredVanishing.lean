module

public import M9StacksIntegration.MukaiDualSpanSections
public import M9StacksIntegration.MukaiBundleTensor
public import M9StacksIntegration.InvertibleExtCancellation

/-!
# The actual degree filtration forces Mukai's section vanishing

An actual extension of line bundles of degrees below `deg α` admits no
map from `α`. After tensoring by its actual inverse, the original Hom
space is the actual native zeroth cohomology of `α⁻¹ ⊗ Q`.

For the geometric extension in Mukai (5.2), the outer degrees are two
and six, whereas `deg α = 8`. This route proves the vanishing in Lemma
5.1(2) uniformly, including isomorphic and nonisomorphic α and β.
It does not assume or construct the needed length-two divisor or its
geometric extension.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace M9Native.MukaiFilteredVanishing

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundleDeterminant
open M9Native.InvertibleExtCancellation

variable {k : Type u} [Field k] {X : Scheme.{u}}

local instance nativeHasExt (X : Scheme.{u}) : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules

/-- A nonzero morphism of the actual line bundles cannot decrease their
native degree. -/
theorem hom_eq_zero_of_degree_lt (f : X ⟶ Spec (.of k))
    [IsCurve k f] [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (α L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property α]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (hdeg : invertibleCurveDegree k f hdim L < invertibleCurveDegree k f hdim α)
    (φ : α ⟶ L) : φ = 0 := by
  by_contra hφ
  exact (not_le_of_gt hdeg)
    (invertibleCurveDegree_le_of_hom_ne_zero k f hdim α L φ hφ)

/-- Exactness of an actual extension and the two strict native degree
bounds force every map from α into its middle term to vanish. -/
theorem extension_hom_eq_zero_of_outer_degrees_lt
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (α : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property α]
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property S.X₁]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property S.X₃]
    (h₁ : invertibleCurveDegree k f hdim S.X₁ < invertibleCurveDegree k f hdim α)
    (h₃ : invertibleCurveDegree k f hdim S.X₃ < invertibleCurveDegree k f hdim α)
    (φ : α ⟶ S.X₂) : φ = 0 := by
  let := hS.mono_f
  have hφg : φ ≫ S.g = 0 := hom_eq_zero_of_degree_lt f hdim α S.X₃ h₃ _
  let ψ := hS.exact.lift φ hφg
  have hψ : ψ = 0 := hom_eq_zero_of_degree_lt f hdim α S.X₁ h₁ ψ
  exact (hS.exact.lift_f φ hφg).symm.trans (by
    change ψ ≫ S.f = 0
    rw [hψ, zero_comp])

/-- Inverse tensoring is the actual native Hom-to-cohomology equivalence
in degree zero. Vanishing is transported without a scalar convention
or an additional geometric hypothesis. -/
theorem inverseTwist_cohomology_zero_subsingleton_of_hom_eq_zero
    (f : X ⟶ Spec (.of k)) (α Q : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property α]
    (h : ∀ φ : α ⟶ Q, φ = 0) :
    Subsingleton (cohomologyOverField k f
      (Scheme.Modules.tensorObj Q (Scheme.Modules.tensorInverse α)) 0) := by
  let e : (α ⟶ Q) ≃+
      cohomologyOverField k f (Scheme.Modules.tensorObj Q (Scheme.Modules.tensorInverse α)) 0 :=
    (Ext.addEquiv₀ (X := α) (Y := Q)).symm.trans
      (invertibleExtCohomologyAddEquiv k f α Q 0)
  exact ⟨fun a c => e.symm.injective ((h (e.symm a)).trans (h (e.symm c)).symm)⟩

/-- The same vanishing for the literal dual-line-bundle twist, with its
factor placed first as in Mukai's notation `α⁻¹ Q`. -/
theorem dualTwist_cohomology_zero_subsingleton_of_hom_eq_zero
    (f : X ⟶ Spec (.of k)) (α Q : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property α]
    (h : ∀ φ : α ⟶ Q, φ = 0) :
    Subsingleton (cohomologyOverField k f
      (Scheme.Modules.tensorObj (dualSheaf α) Q) 0) := by
  let hzero := inverseTwist_cohomology_zero_subsingleton_of_hom_eq_zero f α Q h
  let eα : Scheme.Modules.tensorInverse α ≅ dualSheaf α :=
    tensorInverseNativeIso α _ (inverseTensorUnitIso α)
  let e : Scheme.Modules.tensorObj Q (Scheme.Modules.tensorInverse α) ≅
      Scheme.Modules.tensorObj (dualSheaf α) Q :=
    tensorIso (Iso.refl Q) eα ≪≫
      Stacks.SheafOfModules.Invertible.tensorProductBraiding X.presheaf
        X.ringCatSheaf.property Q (dualSheaf α)
  let eH := (cohomologyOverFieldIso k f e 0).toLinearEquiv
  exact ⟨fun a c => eH.symm.injective (hzero.elim _ _)⟩

/-- The actual outer-degree calculation `2,6 < 8` proves the native
section vanishing for any actual extension of these line bundles. -/
theorem dualTwist_cohomology_zero_subsingleton_of_degrees_two_six_eight
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (α : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property α]
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property S.X₁]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property S.X₃]
    (hα : invertibleCurveDegree k f hdim α = 8)
    (h₁ : invertibleCurveDegree k f hdim S.X₁ = 2)
    (h₃ : invertibleCurveDegree k f hdim S.X₃ = 6) :
    Subsingleton (cohomologyOverField k f
      (Scheme.Modules.tensorObj (dualSheaf α) S.X₂) 0) :=
  dualTwist_cohomology_zero_subsingleton_of_hom_eq_zero f α S.X₂
    (extension_hom_eq_zero_of_outer_degrees_lt f hdim α hS
      (by rw [h₁, hα]; decide) (by rw [h₃, hα]; decide))

end M9Native.MukaiFilteredVanishing
