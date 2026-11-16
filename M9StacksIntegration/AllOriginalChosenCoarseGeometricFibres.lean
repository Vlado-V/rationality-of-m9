module

public import M9StacksIntegration.AllTestOriginalGeometricFamilyModel
public import M9StacksIntegration.BoundedOriginalFamilyCoarseInjectivity
public import M9StacksIntegration.AllTestNativeOriginalPropertyReflection
public import M9StacksIntegration.OriginalClassifierNativeFamilyAgreement

/-!
# Full-original geometric fibres of the actual chosen coarse classifier

The original algebraically closed extension field is arbitrary. Actual
bounded geometric family models and a simultaneous model of their actual
original coarse sections give a common bounded geometric base. Genuine
bounded coarse injectivity there, followed by full-original Cartesian
pullback uniqueness over the same field map, recovers a whole-family
isomorphism over the original extension field.

The classifier is on the same actual chosen original coarse presheaf. Its
only comparison input is agreement with the actual bounded value on every
original family over every bounded base. No geometric-fibre conclusion,
membership of the original field, or finite model is supplied.
-/

set_option autoImplicit false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
attribute [local implicit_reducible] AlgebraicGeometry.schemeSpace
  AlgebraicGeometry.schemeSpaceMap

namespace M9Native.AllOriginalChosenCoarseGeometricFibres
open M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AllTestFamilyPullback
  M9StacksIntegration.AllTestOriginalFamilyCategory
  M9StacksIntegration.AllTestAffineClassifierExtension
  M9StacksIntegration.AllTestOriginalGeometricFamilyModel
  M9StacksIntegration.AllTestNativeOriginalFunctor
  M9StacksIntegration.AllTestNativeOriginalPullbacks
  M9StacksIntegration.AllTestNativeOriginalPropertyReflection
  M9StacksIntegration.AllTestBoundedOriginalRecovery

universe u

private theorem cartesian_postcompose_iso {C : Type*} [Category C]
    {W X Y Z : C} {r : W ⟶ X} {p : W ⟶ Y} {q : X ⟶ Z} {a : Y ⟶ Z}
    (h : IsPullback r p q a) {X' : C} (e : X ≅ X') (q' : X' ⟶ Z)
    (he : e.hom ≫ q' = q) : IsPullback (r ≫ e.hom) p q' a := by
  have hi : IsPullback e.hom q q' (𝟙 Z) :=
    IsPullback.of_horiz_isIso ⟨he.trans (Category.comp_id q).symm⟩
  simpa only [Category.comp_id] using h.paste_horiz hi

private theorem familyIsomorphic_of_same_cartesian_target
    (K : Type u) [Field K] (g : ℕ) {T U : M9StandaloneDraft.Schemes K}
    (F G : M9StandaloneDraft.Family K T g) (H : M9StandaloneDraft.Family K U g)
    (v : T ⟶ U) (rF : F.total.obj ⟶ H.total.obj) (rG : G.total.obj ⟶ H.total.obj)
    (hF : IsPullback rF F.projection H.projection (yoneda.map v))
    (hG : IsPullback rG G.projection H.projection (yoneda.map v)) :
    M9StandaloneDraft.FamilyIsomorphic K F G := by
  obtain ⟨eF, heF⟩ := familyIsomorphic_pullback_of_cartesian K g F H v rF hF
  obtain ⟨eG, heG⟩ := familyIsomorphic_pullback_of_cartesian K g G H v rG hG
  have hi : eG.inv ≫ G.projection = (pullbackFamily K H v).projection := by
    rw [Iso.inv_comp_eq]
    exact heG.symm
  refine ⟨eF ≪≫ eG.symm, ?_⟩
  change (eF.hom ≫ eG.inv) ≫ G.projection = F.projection
  rw [Category.assoc, hi]
  exact heF

/-- Equal values of the actual chosen full-original classifier identify
whole original families over every algebraically closed extension field. -/
theorem familyIsomorphic_of_value_eq
    (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
    (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
    (g : ℕ) (hg : 2 ≤ g)
    (c : M9StandaloneDraft.Classifier K g
      ((originalPresheafFunctor K B hK).obj
        (M9StacksIntegration.GenusNineCoarseOverField.coarseSpace B hZ K hK g hg)))
    (hB : ∀ (T : BigFppfOver B (Spec (.of K)) hK)
      (H : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g),
      c.value ((boundedInclusion B K hK).obj T) H =
        BoundedOriginalFamilyCoarseValue.originalValue B hZ K hK g hg H)
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L]
    (F G : M9StandaloneDraft.Family K (M9StandaloneDraft.FieldPoint K L) g)
    (hFG : c.value (M9StandaloneDraft.FieldPoint K L) F =
      c.value (M9StandaloneDraft.FieldPoint K L) G) :
    M9StandaloneDraft.FamilyIsomorphic K F G := by
  obtain ⟨Ω, fΩ, acΩ, hΩ, sΩ, FΩ, wF, rF, hrF⟩ :=
    exists_bounded_geometric_family_model K B hK g L F
  letI : Field Ω := fΩ
  letI : IsAlgClosed Ω := acΩ
  let U := siteObject B (Spec (.of K)) hK hΩ sΩ
  obtain ⟨Ψ, fΨ, acΨ, hΨ, sΨ, GΨ, wG, rG, hrG⟩ :=
    exists_bounded_geometric_family_model K B hK g L G
  letI : Field Ψ := fΨ
  letI : IsAlgClosed Ψ := acΨ
  let V := siteObject B (Spec (.of K)) hK hΨ sΨ
  let M := M9StacksIntegration.GenusNineCoarseOverField.coarseSpace B hZ K hK g hg
  let O := originalPresheafFunctor K B hK
  let cf : yoneda.obj ((boundedInclusion B K hK).obj U) ⟶ O.obj M :=
    yonedaEquiv.symm (c.value ((boundedInclusion B K hK).obj U) FΩ)
  let cg : yoneda.obj ((boundedInclusion B K hK).obj V) ⟶ O.obj M :=
    yonedaEquiv.symm (c.value ((boundedInclusion B K hK).obj V) GΨ)
  let f : schemeSpace U ⟶ M := nativeChartOfOriginal K B hK M U cf
  let j : schemeSpace V ⟶ M := nativeChartOfOriginal K B hK M V cg
  have hf : originalChart K B hK M U f.hom = cf :=
    originalChart_nativeChartOfOriginal K B hK M U cf
  have hj : originalChart K B hK M V j.hom = cg :=
    originalChart_nativeChartOfOriginal K B hK M V cg
  have hcharts : (originalChart K B hK M U f.hom).app
        (op (M9StandaloneDraft.FieldPoint K L)) wF =
      (originalChart K B hK M V j.hom).app
        (op (M9StandaloneDraft.FieldPoint K L)) wG := by
    rw [hf, hj]
    change (O.obj M).map wF.op (c.value ((boundedInclusion B K hK).obj U) FΩ) =
      (O.obj M).map wG.op (c.value ((boundedInclusion B K hK).obj V) GΨ)
    exact (c.naturality _ _ wF FΩ F rF hrF).trans
      (hFG.trans (c.naturality _ _ wG GΨ G rG hrG).symm)
  obtain ⟨P, fP, acP, hP, sP, a, b, v, hab, hva, hvb⟩ :=
    SimultaneousNativeGeometricModel.exists_simultaneous_model K B hK M U V
      f.hom j.hom L wF wG hcharts
  letI : Field P := fP
  letI : IsAlgClosed P := acP
  let Q := siteObject B (Spec (.of K)) hK hP sP
  let qa := (boundedInclusion B K hK).map a
  let qb := (boundedInclusion B K hK).map b
  let FQ := pullbackFamily K FΩ qa
  let GQ := pullbackFamily K GΨ qb
  let pF := pullbackMap K g
    (⟨(boundedInclusion B K hK).obj U, FΩ⟩ : CurveObject K g) qa
  let pG := pullbackMap K g
    (⟨(boundedInclusion B K hK).obj V, GΨ⟩ : CurveObject K g) qb
  have hchartsQ := congrArg (originalChart K B hK M Q) hab
  rw [SimultaneousNativeGeometricModel.originalChart_precompose K B hK a f,
    SimultaneousNativeGeometricModel.originalChart_precompose K B hK b j,
    hf, hj] at hchartsQ
  have hvalues := congrArg
    (fun η => η.app (op ((boundedInclusion B K hK).obj Q)) (𝟙 _)) hchartsQ
  change (O.obj M).map qa.op (c.value ((boundedInclusion B K hK).obj U) FΩ) =
    (O.obj M).map qb.op (c.value ((boundedInclusion B K hK).obj V) GΨ) at hvalues
  have hcoarse : c.value ((boundedInclusion B K hK).obj Q) FQ =
      c.value ((boundedInclusion B K hK).obj Q) GQ := by
    exact (c.naturality _ _ qa FΩ FQ pF.totalMap pF.cartesian).symm.trans
      (hvalues.trans (c.naturality _ _ qb GΨ GQ pG.totalMap pG.cartesian))
  rw [hB Q FQ, hB Q GQ] at hcoarse
  let e := originalNativeRestrictionSmallIso K B hK M.obj M.property
  have hnative : BoundedOriginalFamilyCoarseValue.nativeValue B hZ K hK g hg
        (T := Q) FQ =
      BoundedOriginalFamilyCoarseValue.nativeValue B hZ K hK g hg (T := Q) GQ := by
    apply (ConcreteCategory.bijective_of_isIso (e.inv.app (op Q))).1
    exact hcoarse
  obtain ⟨eQ, heQ⟩ :=
    BoundedOriginalFamilyCoarseInjectivity.familyIsomorphic_of_nativeValue_eq
      B hZ K hK g hg P Q (Iso.refl _) FQ GQ hnative
  let φF : (⟨M9StandaloneDraft.FieldPoint K L, F⟩ : CurveObject K g) ⟶
      ⟨(boundedInclusion B K hK).obj U, FΩ⟩ := ⟨wF, rF, hrF⟩
  let φG : (⟨M9StandaloneDraft.FieldPoint K L, G⟩ : CurveObject K g) ⟶
      ⟨(boundedInclusion B K hK).obj V, GΨ⟩ := ⟨wG, rG, hrG⟩
  let χF := cartesianFactor K g pF φF v hva
  let χG := cartesianFactor K g pG φG v hvb
  have hχF : χF.baseMap = v := rfl
  have hχG : χG.baseMap = v := rfl
  have hFcart := cartesian_postcompose_iso χF.cartesian eQ GQ.projection heQ
  rw [hχF] at hFcart
  have hGcart := χG.cartesian
  rw [hχG] at hGcart
  exact familyIsomorphic_of_same_cartesian_target K g F G GQ v
    (χF.totalMap ≫ eQ.hom) χG.totalMap hFcart hGcart

/-- The actual chosen classifier identifies exactly the isomorphism classes
of whole original families at every original algebraically closed field. -/
theorem value_eq_iff_familyIsomorphic
    (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
    (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
    (g : ℕ) (hg : 2 ≤ g)
    (c : M9StandaloneDraft.Classifier K g
      ((originalPresheafFunctor K B hK).obj
        (M9StacksIntegration.GenusNineCoarseOverField.coarseSpace B hZ K hK g hg)))
    (hB : ∀ (T : BigFppfOver B (Spec (.of K)) hK)
      (H : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g),
      c.value ((boundedInclusion B K hK).obj T) H =
        BoundedOriginalFamilyCoarseValue.originalValue B hZ K hK g hg H)
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L]
    (F G : M9StandaloneDraft.Family K (M9StandaloneDraft.FieldPoint K L) g) :
    c.value (M9StandaloneDraft.FieldPoint K L) F =
      c.value (M9StandaloneDraft.FieldPoint K L) G ↔
        M9StandaloneDraft.FamilyIsomorphic K F G :=
  ⟨familyIsomorphic_of_value_eq B hZ K hK g hg c hB L F G,
    OriginalClassifierNativeFamilyAgreement.classifier_value_of_familyIsomorphic K c⟩

end M9Native.AllOriginalChosenCoarseGeometricFibres
