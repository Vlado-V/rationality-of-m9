module

public import M9StacksIntegration.LagrangianFiveCutCanonical

/-!
# Native genus of every original field-valued section fibre

The original family already satisfies its genuine all-field curve
condition. This identifies the native genus of every actual field
fibre with the computed family genus and hence with the actual LG
sixfold degree. No numerical genus or degree premise is supplied.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u
namespace M9Native.UniversalLagrangianFieldGenus
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LagrangianLinearSectionGenericSmooth

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]

/-- Every actual field-valued fibre has the same native cohomological
genus, with the original field action and projection retained. -/
theorem field_genus_eq_fibreGenus
    {L : Type u} [Field L] (p : Spec (.of L) ⟶ (goodOpen K).toScheme) :
    genus (pullback.snd (restrictedProjection K) p) =
      UniversalLagrangianNativeGenus.fibreGenus K := by
  exact ((UniversalLagrangianNativeGenus.original_schemeCurve K).2.2.2 L p).2

/-- The genuine genus-degree relation holds on every original field
fibre, before any numerical calculation of the LG degree. -/
theorem field_genus_degree_relation
    {L : Type u} [Field L] (p : Spec (.of L) ⟶ (goodOpen K).toScheme) :
    2 * (genus (pullback.snd (restrictedProjection K) p) : ℤ) - 2 =
      degreeWithRespectTo K (LagrangianGrassmannian.projection K)
        (𝟙 (LagrangianGrassmannian.space K)) 6 (LagrangianIntegral.space_dimension K)
        (LagrangianPluckerQuotient.determinantLine K)
        (LagrangianDegree.determinantLine_modulesIsAmple K) := by
  rw [field_genus_eq_fibreGenus K p]
  exact LagrangianFiveCutCanonical.family_genus_degree_relation K

end M9Native.UniversalLagrangianFieldGenus
