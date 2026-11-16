module

public import M9StacksIntegration.AllTestRelativeFamilyModel
public import M9StacksIntegration.SimultaneousNativeGeometricModel
public import M9StacksIntegration.AllTestAffineClassifierExtension

/-!
# Bounded algebraically closed models of original geometric families

The input is an arbitrary original family over an arbitrary algebraically
closed extension field. An actual finite K-stage model and an actual
simultaneous geometric model construct a bounded algebraically closed
field, a family over that field, and the full original Cartesian arrow.
The original field need not belong to the chosen native site.
-/

set_option autoImplicit false
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
attribute [local implicit_reducible] AlgebraicGeometry.schemeSpace
  AlgebraicGeometry.schemeSpaceMap

namespace M9StacksIntegration.AllTestOriginalGeometricFamilyModel
open AllTestBoundedCharts AllTestRelativeFamilyModel
  AllTestFamilyPullback AllTestOriginalFamilyCategory AllTestAffineClassifierExtension

universe u
variable (K : Type u) [Field K]

/-- An actual original Cartesian square identifies its source family with
the actual original pullback, including nonschematic total spaces. -/
theorem familyIsomorphic_pullback_of_cartesian (g : ℕ)
    {T U : M9StandaloneDraft.Schemes K}
    (F : M9StandaloneDraft.Family K T g) (G : M9StandaloneDraft.Family K U g)
    (w : T ⟶ U) (r : F.total.obj ⟶ G.total.obj)
    (hcart : IsPullback r F.projection G.projection (yoneda.map w)) :
    M9StandaloneDraft.FamilyIsomorphic K F (pullbackFamily K G w) := by
  let p := pullbackMap K g (⟨U, G⟩ : CurveObject K g) w
  refine ⟨hcart.isoIsPullback G.total.obj (yoneda.obj T) p.cartesian, ?_⟩
  exact hcart.isoIsPullback_hom_snd G.total.obj (yoneda.obj T) p.cartesian

/-- EVERY original geometric family is the actual base change of a family
over a bounded algebraically closed field, with the SAME original field map. -/
theorem exists_bounded_geometric_family_model
    (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K))) (g : ℕ)
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L]
    (F : M9StandaloneDraft.Family K (M9StandaloneDraft.FieldPoint K L) g) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (hΩ : B.Contains (Spec (.of Ω))) (sΩ : Spec (.of Ω) ⟶ Spec (.of K))
      (FΩ : M9StandaloneDraft.Family K
        ((boundedInclusion B K hK).obj (siteObject B (Spec (.of K)) hK hΩ sΩ)) g)
      (w : M9StandaloneDraft.FieldPoint K L ⟶
        (boundedInclusion B K hK).obj (siteObject B (Spec (.of K)) hK hΩ sΩ))
      (r : F.total.obj ⟶ FΩ.total.obj),
      IsPullback r F.projection FΩ.projection (yoneda.map w) := by
  obtain ⟨i, Fi, ri, hi, hri⟩ :=
    exists_original_family_model_in_field_site K L B hK g F
  let Ui : BigFppfOver B (Spec (.of K)) hK :=
    siteObject B (Spec (.of K)) hK hi ((AdjoinFinset.specToBase K L).app i)
  let T := (boundedInclusion B K hK).obj Ui
  let x : M9StandaloneDraft.FieldPoint K L ⟶ T :=
    Over.homMk ((AdjoinFinset.specCone K L).π.app i)
      (AdjoinFinset.specCone_π_comp K L i)
  obtain ⟨Ω, fΩ, acΩ, hΩ, sΩ, a, _, w, _, hwa, _⟩ :=
    M9Native.SimultaneousNativeGeometricModel.exists_simultaneous_model K B hK
      (schemeSpace Ui) Ui Ui (𝟙 _) (𝟙 _) L x x rfl
  let : Field Ω := fΩ
  let : IsAlgClosed Ω := acΩ
  let q := (boundedInclusion B K hK).map a
  let p := pullbackMap K g (⟨T, Fi⟩ : CurveObject K g) q
  let ψ : (⟨M9StandaloneDraft.FieldPoint K L, F⟩ : CurveObject K g) ⟶ ⟨T, Fi⟩ :=
    ⟨x, ri, hri⟩
  let χ := cartesianFactor K g p ψ w hwa
  exact ⟨Ω, fΩ, acΩ, hΩ, sΩ, pullbackFamily K Fi q, w, χ.totalMap, χ.cartesian⟩

/-- The bounded model also recovers the original family by a genuine
same-base family isomorphism to its actual original pullback. -/
theorem exists_bounded_geometric_family_model_isomorphic
    (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K))) (g : ℕ)
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L]
    (F : M9StandaloneDraft.Family K (M9StandaloneDraft.FieldPoint K L) g) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (hΩ : B.Contains (Spec (.of Ω))) (sΩ : Spec (.of Ω) ⟶ Spec (.of K))
      (FΩ : M9StandaloneDraft.Family K
        ((boundedInclusion B K hK).obj (siteObject B (Spec (.of K)) hK hΩ sΩ)) g)
      (w : M9StandaloneDraft.FieldPoint K L ⟶
        (boundedInclusion B K hK).obj (siteObject B (Spec (.of K)) hK hΩ sΩ))
      (r : F.total.obj ⟶ FΩ.total.obj),
      IsPullback r F.projection FΩ.projection (yoneda.map w) ∧
        M9StandaloneDraft.FamilyIsomorphic K F (pullbackFamily K FΩ w) := by
  obtain ⟨Ω, fΩ, acΩ, hΩ, sΩ, FΩ, w, r, hr⟩ :=
    exists_bounded_geometric_family_model K B hK g L F
  exact ⟨Ω, fΩ, acΩ, hΩ, sΩ, FΩ, w, r, hr,
    familyIsomorphic_pullback_of_cartesian K g F FΩ w r hr⟩

end M9StacksIntegration.AllTestOriginalGeometricFamilyModel
