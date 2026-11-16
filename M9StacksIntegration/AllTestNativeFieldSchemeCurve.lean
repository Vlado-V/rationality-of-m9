module

public import M9StacksIntegration.AllTestNativeFieldSchemeModel
public import M9StacksIntegration.AllTestSchematicGlobalFunctionsReflection
public import M9StacksIntegration.AllTestSchemeCurveConstants
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesOfGenus
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Actual native smooth-genus field objects give ORIGINAL all-field curves

Native universal H0 gives the actual original constants map. Native smooth
relative dimension one gives the original dimension/smoothness. The native
fibre-genus condition at the IDENTITY field point gives the actual original
genus via its genuine represented Cartesian fibre, without any cohomological
rank premise. The proved original field-geometry theorem then supplies its
FULL original all-field H1 condition. This is an actual field-object factory,
not the full all-test coarse theorem.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestNativeFieldSchemeCurve
open AllTestSchematicGlobalFunctionsReflection AllTestSchemeCurveConstants
universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- Literal pinned native field-scheme smooth-dimension comparison,
isolated from the unrelated large genus-decomposition provider. -/
theorem scheme_smoothDimOne_iff {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K))) (X : Over (Spec (.of K))) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (hne : Nonempty X.left) :
    IsSmoothDimOneFamily B hZ (curveFamilyOfScheme X B hZ hK hdim) ↔
      Smooth X.hom ∧ TopologicalSpace.Equidimensional X.left ∧
        topologicalKrullDim X.left = 1 :=
  isSmoothDimOneFamily_curveFamilyOfSchemeMorphism_iff B hZ
    (integerSiteMap B hZ (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hK) hK X.hom)
    (inferInstance : Flat X.hom) ‹_› (inferInstance : LocallyOfFinitePresentation X.hom)
    (Space.isQuasiCompact_yoneda_map_of_quasiCompact B integerBase hZ _
      (inferInstanceAs (QuasiCompact X.hom)))
    ((Space.isSeparated_yoneda_map_iff B integerBase hZ _).2
      (inferInstanceAs (IsSeparated X.hom)))
    ((Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ _).2
      (inferInstanceAs (QuasiSeparated X.hom))) hdim K rfl hne

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The ACTUAL native genus condition at the IDENTITY field point gives the
ORIGINAL scheme's actual genus. No genus or finite-rank premise is supplied. -/
theorem genus_of_native_fibreGenus {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K))) (X : Over (Spec (.of K))) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ)
    (hgen : CurveFamily.HasFieldPointFibreGenus B hZ
      (curveFamilyOfScheme X B hZ hK hdim) g) : genus X.hom = g := by
  let hX : B.Contains X.left := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hK
  let U := integerSiteObject B hZ hX
  let T := integerSiteObject B hZ hK
  let q : U ⟶ T := integerSiteMap B hZ hX hK X.hom
  let p₀ : Space.FieldValuedPoint B integerBase hZ
      (schemeSpace (curveFamilyOfScheme X B hZ hK hdim).base).obj :=
    ⟨K, hK, specULiftZIsTerminal.from _, 𝟙 _⟩
  obtain ⟨V, v, f, hpb, hg⟩ := hgen p₀
  let f' : yoneda.obj V ⟶ yoneda.obj U := f
  let r : V ⟶ U := yoneda.preimage f'
  have hr : yoneda.map r = f' := yoneda.map_preimage f'
  have hval : yonedaEquiv.symm p₀.value = yoneda.map (𝟙 T) :=
    yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map _).symm
  have hpb' : IsPullback (yoneda.map r) (yoneda.map v) (yoneda.map q) (yoneda.map (𝟙 T)) := by
    rw [hr]
    have hpb₀ : IsPullback f' (yoneda.map v) (yoneda.map q) (yonedaEquiv.symm p₀.value) := hpb
    exact hval ▸ hpb₀
  have hn : IsPullback r v q (𝟙 T) := hpb'.of_map_of_faithful yoneda
  have hs := hn.map (BigFppfOver.toScheme B integerBase hZ)
  have hid : (BigFppfOver.toScheme B integerBase hZ).map (𝟙 T) =
      Spec.map (CommRingCat.ofHom (algebraMap K K)) := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    exact (BigFppfOver.toScheme B integerBase hZ).map_id T
  rw [hid] at hs
  exact (genus_baseChange K K ((BigFppfOver.toScheme B integerBase hZ).map r)
    ((BigFppfOver.toScheme B integerBase hZ).map v) X.hom hs).symm.trans hg

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An ACTUAL represented native smooth-genus object proves the complete
ORIGINAL all-field SchemeCurve predicate on the SAME original map. -/
theorem schemeCurve_of_native_membership {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K))) (X : Over (Spec (.of K))) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ)
    (hF : IsSmoothH0FamilyOfFibreGenus B hZ g (curveFamilyOfScheme X B hZ hK hdim)) :
    M9StandaloneDraft.SchemeCurve X.hom g := by
  let hX : B.Contains X.left := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hK
  let U := integerSiteObject B hZ hX
  let q := integerSiteMap B hZ hX hK X.hom
  have hc' := isIso_constants_of_native_H0_represented B hZ
    (curveFamilyOfScheme X B hZ hK hdim) hF.1.2 U (Iso.refl _) q
    (Category.id_comp _) K rfl
  have hc : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ X.hom.appTop) := by
    change IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ (X.hom ≫ 𝟙 (Spec (.of K))).appTop) at hc'
    rw [Category.comp_id] at hc'
    exact hc'
  have hne : Nonempty X.left := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    have : Subsingleton Γ(X.left, ⊤) := inferInstance
    let : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ X.hom.appTop) := hc
    have hinj := (ConcreteCategory.bijective_of_isIso
      ((Scheme.ΓSpecIso (.of K)).inv ≫ X.hom.appTop)).1
    exact zero_ne_one (hinj (Subsingleton.elim _ _) : (0 : K) = 1)
  obtain ⟨hsm, _, hd⟩ := (scheme_smoothDimOne_iff B hZ hK X hdim hne).mp hF.1.1
  exact schemeCurve_of_native_field_geometry X.hom hsm hd hc
    (genus_of_native_fibreGenus B hZ hK X hdim g hF.2)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- EVERY actual native smooth-genus family over a field has an ORIGINAL
proper scheme curve model satisfying the FULL all-field H1 condition, with
an actual SAME-base native family isomorphism. No original model is assumed. -/
theorem exists_original_schemeCurve_of_native_field_family
    {K : Type u} [Field K] (hK : B.Contains (Spec (.of K)))
    (F : CurveFamily B hZ) (hbase : F.base = integerSiteObject B hZ hK) (g : ℕ)
    (hF : IsSmoothH0FamilyOfFibreGenus B hZ g F) :
    ∃ (X : Over (Spec (.of K))) (hp : IsProper X.hom)
      (hdim : topologicalKrullDim X.left ≤ 1),
      M9StandaloneDraft.SchemeCurve X.hom g ∧
      ∃ e : F ≅ @curveFamilyOfScheme K _ X hp B hZ hK hdim,
        e.hom.baseMap = eqToHom hbase := by
  obtain ⟨X, hp, hdim, e, he⟩ :=
    AllTestNativeFieldSchemeModel.exists_iso_curveFamilyOfScheme_over_base_eq hK F hbase
  let : IsProper X.hom := hp
  have hX := CurveFamily.isSmoothH0FamilyOfFibreGenus_of_hom e.inv hF
  exact ⟨X, hp, hdim, schemeCurve_of_native_membership B hZ hK X hdim g hX, e, he⟩

end M9StacksIntegration.AllTestNativeFieldSchemeCurve
