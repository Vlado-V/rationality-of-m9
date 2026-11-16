module

public import M9StacksIntegration.NativeCurveFamilyOpenStageDescent
public import M9StacksIntegration.AllTestNativeFamilyMembership
public import M9StacksIntegration.AllTestNativeOriginalFamily
public import M9StacksIntegration.AllTestNativeFamilyFull

/-!
# ACTUAL full-original relative affine family models

The actual native providers and all preceding family constructions now have
ordinary checked objects. This newly activated integration source needs its
own direct and fresh checks before it is a checked provider.

The intended endpoint has an ORIGINAL family on Spec A as input, and
constructs an ORIGINAL genus-g family on a relative K-finite-type stage,
with a genuine Cartesian family map on ALL original tests. The stage is
contained in EVERY selected SpecK-containing site, with no containment
relation between the ambient sites. The original K-coefficient map is
retained literally. No model, family-equivalence, genus openness, native
membership, chart existence or classifier premise is supplied.
-/

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestRelativeFamilyModel
open AllTestBoundedCharts AllTestNativeCurveFamily AllTestNativeOriginalFamily
universe u

/-- Actual ORIGINAL affine-family approximation with full original
Cartesian square, true genus property, and actual relative K-base map. -/
theorem exists_relative_small_original_family
    (K A : Type u) [Field K] [CommRing A] [Algebra K A]
    (B₀ B₁ : BigFppfSite.{u})
    (hK₀ : B₀.Contains (Spec (.of K))) (hK₁ : B₁.Contains (Spec (.of K)))
    (hA₁ : B₁.Contains (Spec (.of A))) (hZ₁ : B₁.Contains integerBase)
    (g : ℕ)
    (F : M9StandaloneDraft.Family K
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A)))) g) :
    ∃ (i : (Finset A)ᵒᵖ)
      (Fi : M9StandaloneDraft.Family K
        (Over.mk ((AdjoinFinset.specToBase K A).app i)) g)
      (r : F.total.obj ⟶ Fi.total.obj),
      B₀.Contains ((AdjoinFinset.specDiagram K A).obj i) ∧
      IsPullback r F.projection Fi.projection
        (yoneda.map (Over.homMk ((AdjoinFinset.specCone K A).π.app i)
          (AdjoinFinset.specCone_π_comp K A i))) := by
  let k := fieldToInteger B₁ hZ₁ K hK₁
  let TA := siteObject B₁ (Spec (.of K)) hK₁ hA₁
    (Spec.map (CommRingCat.ofHom (algebraMap K A)))
  let G := nativeCurveFamily B₁ hZ₁ K hK₁ (T := TA) F
  have hG : G.base = (BigAffineFppf.inclusion B₁ integerBase hZ₁).obj
      (NativeRelativeAffineRebase.coneOver K A B₁ hK₁ integerBase hZ₁ k hA₁).pt := rfl
  have hPG : IsSmoothH0FamilyOfFibreGenus B₁ hZ₁ g G :=
    AllTestNativeFamilyMembership.nativeCurveFamily_membership B₁ hZ₁ K hK₁ (T := TA) (g := g) F
  obtain ⟨i, Gi, hGi, δ, hPGi, hδ, hsmall⟩ :=
    NativeCurveFamilyOpenStageDescent.exists_hom_to_relative_small_base_with_property
      K A B₀ B₁ hK₀ hK₁ hA₁ hZ₁ k
      (AllTestNativeFamilyMembership.intrinsic_isOpen B₁ hZ₁ g) G hG hPG
  let Ti := (BigAffineFppf.inclusion B₁ (Spec (.of K)) hK₁).obj
    ((NativeRelativeAffineModels.diagram K A B₁ hK₁).obj i)
  have hbase : Gi.base = nativeBase B₁ hZ₁ K hK₁ Ti := hGi
  let Fi := originalFamily B₁ hZ₁ K hK₁ Ti Gi hbase g hPGi
  let e := originalFamilyNativeIso B₁ hZ₁ K hK₁ Ti Gi hbase g hPGi
  have he : e.hom.baseMap = eqToHom hbase.symm :=
    originalFamilyNativeIso_baseMap B₁ hZ₁ K hK₁ Ti Gi hbase g hPGi
  have hei : e.inv.baseMap = eqToHom hbase := by
    have h := congrArg (fun f : Gi ⟶ Gi => f.baseMap) e.inv_hom_id
    change e.inv.baseMap ≫ e.hom.baseMap = 𝟙 Gi.base at h
    rw [he] at h
    calc
      e.inv.baseMap = e.inv.baseMap ≫ (eqToHom hbase.symm ≫ eqToHom hbase) := by simp
      _ = (e.inv.baseMap ≫ eqToHom hbase.symm) ≫ eqToHom hbase :=
        (Category.assoc _ _ _).symm
      _ = eqToHom hbase := by rw [h, Category.id_comp]
  let a : TA ⟶ Ti := (BigAffineFppf.inclusion B₁ (Spec (.of K)) hK₁).map
    ((NativeRelativeAffineModels.cone K A B₁ hK₁ hA₁).π.app i)
  let δ' : nativeCurveFamily B₁ hZ₁ K hK₁ (T := TA) (g := g) F ⟶
      nativeCurveFamily B₁ hZ₁ K hK₁ (T := Ti) (g := g) Fi := δ ≫ e.inv
  have hδ' : δ'.baseMap = (Over.map k).map a := by
    change δ.baseMap ≫ e.inv.baseMap = _
    rw [hδ, hei]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp,
      Category.comp_id]
    rfl
  obtain ⟨r, ⟨hr, _⟩, _⟩ :=
    AllTestNativeFamilyFull.existsUnique_original_cartesian_lift B₁ hZ₁ K hK₁
      (U := TA) (T := Ti) (g := g) a Fi F δ' hδ'
  exact ⟨i, Fi, r, NativeRelativeAffineModels.contains_stage K A B₀ hK₀ i.unop, hr⟩

/-- EVERY original affine family has a full-original finite K-stage model
inside ANY selected field-containing site. The auxiliary larger site is
constructed from the actual field and affine base, rather than supplied. -/
theorem exists_original_family_model_in_field_site
    (K A : Type u) [Field K] [CommRing A] [Algebra K A]
    (B₀ : BigFppfSite.{u}) (hK₀ : B₀.Contains (Spec (.of K))) (g : ℕ)
    (F : M9StandaloneDraft.Family K
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A)))) g) :
    ∃ (i : (Finset A)ᵒᵖ)
      (Fi : M9StandaloneDraft.Family K
        (Over.mk ((AdjoinFinset.specToBase K A).app i)) g)
      (r : F.total.obj ⟶ Fi.total.obj),
      B₀.Contains ((AdjoinFinset.specDiagram K A).obj i) ∧
      IsPullback r F.projection Fi.projection
        (yoneda.map (Over.homMk ((AdjoinFinset.specCone K A).π.app i)
          (AdjoinFinset.specCone_π_comp K A i))) := by
  obtain ⟨B₁, hB₁⟩ := BigFppfSite.exists_containing
    ({Spec (.of K), Spec (.of A), integerBase} : Set Scheme.{u})
  have hK₁ : B₁.Contains (Spec (.of K)) := hB₁ _ (by simp)
  have hA₁ : B₁.Contains (Spec (.of A)) := hB₁ _ (by simp)
  have hZ₁ : B₁.Contains integerBase := hB₁ _ (by simp)
  exact exists_relative_small_original_family K A B₀ B₁ hK₀ hK₁ hA₁ hZ₁ g F

end M9StacksIntegration.AllTestRelativeFamilyModel
