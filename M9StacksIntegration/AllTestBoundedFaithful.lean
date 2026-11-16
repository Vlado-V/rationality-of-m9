module

public import M9StacksIntegration.AllTestAtlasDescent
public import M9StacksIntegration.AllTestNativeCurveNaturality

/-!
# Actual faithfulness of the original-family comparison

An actual bounded original atlas is locally surjective on the FULL original
site and hence epi as a map of original sheaves. Equality of restricted maps
can be tested on the bounded atlas by Yoneda, and the original sheaf epi then
proves equality everywhere. No fully faithful comparison or classifier is
assumed. The native-arrow consequence also uses the proved faithful actual
lower-shriek extension.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestBoundedFaithful
open AllTestBoundedCharts AllTestBoundedRestriction AllTestAtlasDescent
  AllTestNativeCurveFamily AllTestNativeCurveNaturality
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Bounded restriction is faithful on actual all-test maps FROM an original
family total TO any original sheaf, on the entire original test category. -/
theorem restrictMap_injective_from_family
    {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g)
    (H : M9StandaloneDraft.Presheaves K)
    (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) H)
    {a b : F.total.obj ⟶ H} (hab : restrictMap K B hK a = restrictMap K B hK b) : a = b := by
  obtain ⟨Z, r, he, hs⟩ := exists_bounded_original_atlas K B hK F
  let J := Scheme.fppfTopology.over (M9StandaloneDraft.Base K)
  let Fs : Sheaf J (Type u) := ⟨F.total.obj, F.total.isSheaf⟩
  let Hs : Sheaf J (Type u) := ⟨H, hH⟩
  let rs : J.yoneda.obj ((boundedInclusion B K hK).obj Z) ⟶ Fs := ⟨r⟩
  let as' : Fs ⟶ Hs := ⟨a⟩
  let bs' : Fs ⟶ Hs := ⟨b⟩
  let : Presheaf.IsLocallySurjective J r :=
    isLocallySurjective_of_presheaf_etale_surjective K r he hs
  let : Sheaf.IsLocallySurjective rs := inferInstanceAs (Presheaf.IsLocallySurjective J r)
  have hpre : r ≫ a = r ≫ b := by
    apply yonedaEquiv.injective
    have hx := ConcreteCategory.congr_hom (NatTrans.congr_app hab (op Z))
      (r.app (op ((boundedInclusion B K hK).obj Z)) (𝟙 _))
    exact hx
  have hs' : rs ≫ as' = rs ≫ bs' := by
    apply ObjectProperty.hom_ext
    exact hpre
  have hab' : as' = bs' := (cancel_epi rs).mp hs'
  exact congrArg (fun f => f.hom) hab'

/-- Consequently the actual native total-space map is faithful on original
all-test maps between family totals. Its coefficient extension is the actual
proved faithful lower-shriek, not a field-automorphism quotient. -/
theorem nativeTotalMap_injective
    (hZ : B.Contains integerBase)
    {U T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g)
    (G : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj U) g)
    {a b : G.total.obj ⟶ F.total.obj}
    (hab : nativeTotalMap B hZ K hK F G a = nativeTotalMap B hZ K hK F G b) : a = b := by
  let k := fieldToInteger B hZ K hK
  let L := OverShriek.relocalizePresheafFunctor k
  let : L.Faithful := relocalizePresheaf_faithful k
  apply restrictMap_injective_from_family K B hK G F.total.obj F.total.isSheaf
  apply L.map_injective
  exact congrArg (fun f => f.hom) hab

end M9StacksIntegration.AllTestBoundedFaithful
