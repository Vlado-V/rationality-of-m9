module

public import M9StacksIntegration.AllTestNativeFieldSchemeCurve
public import M9StacksIntegration.AllTestResidueSchemeCurve
public import M9StacksIntegration.NativeSchematicCurveFamily

/-!
# Native smooth-genus schematic families give FULL ORIGINAL curve families

At a field base the actual original scheme is identified with the genuine
model constructed from native membership, over the IDENTITY field map.
For an arbitrary bounded base, pull back to its ACTUAL residue fields,
use the actual field result, and apply proved canonical residue-fibre
recovery to derive ALL original field quantifiers. No original SchemeCurve,
H0/genus/rank/classifier or relative comparison premise is assumed.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestNativeSchematicCurveReflection
open NativeSchematicCurveFamily AllTestNativeFieldSchemeCurve
  AllTestResidueSchemeCurve StandaloneCurveCohomology
universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An actual represented native field family gives the literal ORIGINAL
SchemeCurve condition on the SAME original structural morphism. -/
theorem field_schemeCurve_of_native_membership
    {K : Type u} [Field K] (hK : B.Contains (Spec (.of K)))
    {Z : BigFppfOver B integerBase hZ} (q : Z ⟶ integerSiteObject B hZ hK)
    (hp : IsProper ((BigFppfOver.toScheme B integerBase hZ).map q))
    (hs : SmoothOfRelativeDimension 1 ((BigFppfOver.toScheme B integerBase hZ).map q))
    (g : ℕ) (hF : IsSmoothH0FamilyOfFibreGenus B hZ g
      (properSmoothSchemeFamily B hZ q hp hs)) :
    M9StandaloneDraft.SchemeCurve ((BigFppfOver.toScheme B integerBase hZ).map q) g := by
  let F := properSmoothSchemeFamily B hZ q hp hs
  obtain ⟨X, hpX, hdX, hX, e, he⟩ :=
    exists_original_schemeCurve_of_native_field_family B hZ hK F rfl g hF
  let : IsProper X.hom := hpX
  let hXs : B.Contains X.left := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hK
  let U := integerSiteObject B hZ hXs
  let p : U ⟶ integerSiteObject B hZ hK := integerSiteMap B hZ hXs hK X.hom
  let G := curveFamilyOfScheme X B hZ hK hdX
  let E : yoneda.obj Z ≅ yoneda.obj U :=
    { hom := e.hom.totalMap.hom
      inv := e.inv.totalMap.hom
      hom_inv_id := by exact congrArg (fun f : F ⟶ F => f.totalMap.hom) e.hom_inv_id
      inv_hom_id := by exact congrArg (fun f : G ⟶ G => f.totalMap.hom) e.inv_hom_id }
  let EN : Z ≅ U := Yoneda.fullyFaithful.preimageIso E
  let ES := (BigFppfOver.toScheme B integerBase hZ).mapIso EN
  have heb : e.hom.baseMap = 𝟙 (integerSiteObject B hZ hK) := by
    change e.hom.baseMap = 𝟙 (integerSiteObject B hZ hK) at he
    exact he
  have hw : E.hom ≫ yoneda.map p = yoneda.map q := by
    have h := congrArg (fun f => f.hom) e.hom.cartesian.w
    change E.hom ≫ yoneda.map p = yoneda.map q ≫ yoneda.map e.hom.baseMap at h
    have h' : E.hom ≫ yoneda.map p = yoneda.map q ≫ yoneda.map (𝟙 (integerSiteObject B hZ hK)) := heb ▸ h
    rw [(yoneda (C := BigFppfOver B integerBase hZ)).map_id, Category.comp_id] at h'
    exact h'
  have hn : EN.hom ≫ p = q := by
    apply yoneda.map_injective
    rw [Functor.map_comp]
    change yoneda.map (Yoneda.fullyFaithful.preimage E.hom) ≫ yoneda.map p = yoneda.map q
    rw [Yoneda.fullyFaithful.map_preimage]
    exact hw
  have hES : ES.hom ≫ X.hom = (BigFppfOver.toScheme B integerBase hZ).map q := by
    change (BigFppfOver.toScheme B integerBase hZ).map EN.hom ≫
      (BigFppfOver.toScheme B integerBase hZ).map p = _
    exact ((BigFppfOver.toScheme B integerBase hZ).map_comp EN.hom p).symm.trans
      (congrArg (fun f => (BigFppfOver.toScheme B integerBase hZ).map f) hn)
  exact schemeCurve_of_iso X.hom ((BigFppfOver.toScheme B integerBase hZ).map q) ES hES hX

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Over an ARBITRARY bounded scheme base, native smooth-genus membership
proves the complete ORIGINAL all-field SchemeCurve predicate. -/
theorem schemeCurve_of_native_membership
    {Z T : BigFppfOver B integerBase hZ} (q : Z ⟶ T)
    (hp : IsProper ((BigFppfOver.toScheme B integerBase hZ).map q))
    (hs : SmoothOfRelativeDimension 1 ((BigFppfOver.toScheme B integerBase hZ).map q))
    (g : ℕ) (hF : IsSmoothH0FamilyOfFibreGenus B hZ g
      (properSmoothSchemeFamily B hZ q hp hs)) :
    M9StandaloneDraft.SchemeCurve ((BigFppfOver.toScheme B integerBase hZ).map q) g := by
  let U := BigFppfOver.toScheme B integerBase hZ
  let : IsProper (U.map q) := hp
  let : SmoothOfRelativeDimension 1 (U.map q) := hs
  apply schemeCurve_of_residue_fibres (U.map q) g
  intro t
  let K := (U.obj T).residueField t
  let hK : B.Contains (Spec K) := B.residueField_spec_contains T.left.property t
  let A := integerSiteObject B hZ hK
  let a : A ⟶ T := Over.homMk (ObjectProperty.homMk ((U.obj T).fromSpecResidueField t))
    (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))
  let V := pullback q a
  let b : V ⟶ A := pullback.snd q a
  have hpb := (IsPullback.of_hasPullback q a).map U
  have hpV : IsProper (U.map b) := MorphismProperty.of_isPullback (P := @IsProper) hpb hp
  have hsV : SmoothOfRelativeDimension 1 (U.map b) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1) hpb hs
  let δ : properSmoothSchemeFamily B hZ b hpV hsV ⟶ properSmoothSchemeFamily B hZ q hp hs :=
    { baseMap := a
      totalMap := schemeSpaceMap (pullback.fst q a)
      cartesian := by
        apply IsPullback.of_map_of_faithful (F := ObjectProperty.ι (IsAlgebraicSpace B integerBase hZ))
        exact (IsPullback.of_hasPullback q a).map yoneda }
  have hFV := CurveFamily.isSmoothH0FamilyOfFibreGenus_of_hom δ hF
  have hcv := field_schemeCurve_of_native_membership B hZ hK b hpV hsV g hFV
  let E := hpb.isoPullback
  have he : E.hom ≫ (U.map q).fiberToSpecResidueField t = U.map b := hpb.isoPullback_hom_snd
  have he' : E.inv ≫ U.map b = (U.map q).fiberToSpecResidueField t := by
    rw [← he, Iso.inv_hom_id_assoc]
  exact schemeCurve_of_iso (U.map b) ((U.map q).fiberToSpecResidueField t) E.symm he' hcv

end M9StacksIntegration.AllTestNativeSchematicCurveReflection
