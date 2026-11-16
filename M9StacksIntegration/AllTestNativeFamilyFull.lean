module

public import M9StacksIntegration.AllTestPointedRelocalizeFull
public import M9StacksIntegration.AllTestBoundedFull
public import M9StacksIntegration.AllTestNativeCartesianReflection

/-!
# Actual full cartesian comparison for ORIGINAL nonschematic curve families

Every morphism of the actual native images over a specified ORIGINAL K-base
map uniquely lifts to an actual cartesian morphism on ALL original tests.
The native square forces compatibility with the ORIGINAL coefficient map;
actual pointed relocalization fullness then constructs the map on the K-site,
and actual original atlas descent constructs it on the entire original site.

In particular, native isomorphism classes OVER THE SAME BASE are exactly
literal original FamilyIsomorphic classes. No classifier, equivalence or
field-automorphism quotient is assumed.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestNativeFamilyFull
open AllTestBoundedCharts AllTestBoundedRestriction AllTestBoundedCartesian
  AllTestNativeCurveFamily AllTestNativeCurveNaturality AllTestNativeCartesianReflection
  AllTestPointedRelocalizeFull AllTestBoundedFull AllTestBoundedFaithful
universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual native projection remembers exactly the original coefficient
structure carried by the relocalized original total. -/
theorem nativeProjection_coefficient
    {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    (nativeProjection B hZ K hK F).hom ≫ yoneda.map (baseCoefficientMap B hZ K hK T) =
      OverShriek.relocalizeToYoneda (fieldToInteger B hZ K hK)
        (restrict K B hK F.total.obj) := by
  ext W x
  rcases x with ⟨⟨ψ, s⟩, hψ⟩
  apply Over.OverMorphism.ext
  exact Over.w ((baseMap K B hK T F.projection).app (op (Over.mk ψ)) s)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Every genuine native family arrow over an ORIGINAL K-base map uniquely
lifts to a genuine cartesian arrow on ALL original tests. -/
theorem existsUnique_original_cartesian_lift
    {U T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (a : U ⟶ T)
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g)
    (G : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj U) g)
    (δ : nativeCurveFamily B hZ K hK G ⟶ nativeCurveFamily B hZ K hK F)
    (hδ : δ.baseMap = (Over.map (fieldToInteger B hZ K hK)).map a) :
    ∃! r : G.total.obj ⟶ F.total.obj,
      IsPullback r G.projection F.projection
        (yoneda.map ((boundedInclusion B K hK).map a)) ∧
      nativeTotalMap B hZ K hK F G r = δ.totalMap := by
  let k := fieldToInteger B hZ K hK
  let L := OverShriek.relocalizePresheafFunctor k
  have hcoeff : δ.baseMap ≫ baseCoefficientMap B hZ K hK T =
      baseCoefficientMap B hZ K hK U := by
    rw [hδ]
    apply Over.OverMorphism.ext
    exact Over.w a
  have hw : δ.totalMap.hom ≫ (nativeProjection B hZ K hK F).hom =
      (nativeProjection B hZ K hK G).hom ≫ yoneda.map δ.baseMap :=
    congrArg (fun m => m.hom) δ.cartesian.w
  have hpoint : δ.totalMap.hom ≫ OverShriek.relocalizeToYoneda k
        (restrict K B hK F.total.obj) =
      OverShriek.relocalizeToYoneda k (restrict K B hK G.total.obj) := by
    rw [← nativeProjection_coefficient B hZ K hK F, ← Category.assoc, hw,
      Category.assoc, ← yoneda.map_comp, hcoeff,
      nativeProjection_coefficient B hZ K hK G]
  obtain ⟨n, hn, _⟩ := existsUnique_preimage_of_pointed B (Spec (.of K)) integerBase
    hK hZ k δ.totalMap.hom hpoint
  obtain ⟨r, hr, _⟩ := existsUnique_lift_restrictMap_from_family K B hK G
    F.total.obj F.total.isSheaf n
  have htotal : nativeTotalMap B hZ K hK F G r = δ.totalMap := by
    apply ObjectProperty.hom_ext
    change L.map (restrictMap K B hK r) = δ.totalMap.hom
    rw [hr]
    exact hn
  have hcart : IsPullback (nativeTotalMap B hZ K hK F G r)
      (nativeCurveFamily B hZ K hK G).toBase (nativeCurveFamily B hZ K hK F).toBase
      (schemeSpaceMap ((Over.map k).map a)) := by
    rw [htotal]
    exact hδ ▸ δ.cartesian
  refine ⟨r, ⟨original_cartesian_of_native_cartesian B hZ K hK a F G r hcart, htotal⟩, ?_⟩
  intro r' hr'
  exact AllTestBoundedFaithful.nativeTotalMap_injective K B hK hZ F G (hr'.2.trans htotal.symm)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Native arrows over the identity base identify exactly the ORIGINAL
unpointed curve-family isomorphism classes, retaining the coefficient field. -/
theorem familyIsomorphic_iff_native_identity_arrow
    {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F G : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    M9StandaloneDraft.FamilyIsomorphic K F G ↔
      ∃ δ : nativeCurveFamily B hZ K hK F ⟶ nativeCurveFamily B hZ K hK G,
        δ.baseMap = 𝟙 (nativeBase B hZ K hK T) := by
  constructor
  · rintro ⟨e, he⟩
    have hcart : IsPullback e.hom F.projection G.projection
        (yoneda.map ((boundedInclusion B K hK).map (𝟙 T))) := by
      rw [(boundedInclusion B K hK).map_id, (yoneda (C := M9StandaloneDraft.Schemes K)).map_id]
      exact IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using he⟩
    refine ⟨nativeCartesianMap B hZ K hK (𝟙 T) G F e.hom hcart, ?_⟩
    exact (Over.map (fieldToInteger B hZ K hK)).map_id T
  · rintro ⟨δ, hδ⟩
    have hδ' : δ.baseMap = (Over.map (fieldToInteger B hZ K hK)).map (𝟙 T) :=
      hδ.trans ((Over.map (fieldToInteger B hZ K hK)).map_id T).symm
    obtain ⟨r, ⟨hr, _⟩, _⟩ := existsUnique_original_cartesian_lift B hZ K hK (𝟙 T) G F δ hδ'
    rw [(boundedInclusion B K hK).map_id, (yoneda (C := M9StandaloneDraft.Schemes K)).map_id] at hr
    let : IsIso r := hr.isIso_fst_of_isIso
    refine ⟨asIso r, ?_⟩
    change r ≫ G.projection = F.projection
    simpa only [Category.comp_id] using hr.w

end M9StacksIntegration.AllTestNativeFamilyFull
