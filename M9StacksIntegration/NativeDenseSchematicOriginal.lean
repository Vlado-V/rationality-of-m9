module

public import M9StacksIntegration.AllTestNativeOriginalDenseOpen
public import M9StacksIntegration.AllTestDenseOpenTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusDecent

/-!
# An actual original dense scheme chart from native decency

The native schematic-locus theorem supplies a represented dense open. Its
actual representing object belongs to the SAME bounded site. The proved
native-to-original comparison preserves its actual base map and gives a
literal all-original-test dense open from that actual original scheme.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u
namespace M9StacksIntegration.NativeDenseSchematicOriginal
open AllTestBoundedCharts AllTestNativeOriginalFunctor AllTestNativeOriginalSchemes
  AllTestNativeOriginalPullbacks
attribute [local instance] Space.pointTopology

variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- Native decency produces a genuine dense open map from an actual
representing scheme in the original bounded site. -/
theorem exists_native_dense_scheme
    (X : AlgebraicSpaces B (Spec (.of K)) hK)
    (hdec : Space.IsDecentSpace B (Spec (.of K)) hK X.obj) :
    ∃ (U : BigFppfOver B (Spec (.of K)) hK) (a : yoneda.obj U ⟶ X.obj),
      Space.IsOpenImmersion B (Spec (.of K)) hK a ∧
      DenseRange (Space.pointsMap B (Spec (.of K)) hK (yoneda.obj U) a) := by
  obtain ⟨G, hG, hrep, hd⟩ :=
    Space.exists_denseRange_isRepresentable_isOpenSubspace_of_isDecentSpace
      B (Spec (.of K)) hK X.property hdec
  letI : G.toFunctor.IsRepresentable := hrep
  let U := G.toFunctor.reprX
  let a : yoneda.obj U ⟶ X.obj := G.toFunctor.reprW.hom ≫ G.ι
  have ha : Space.IsOpenImmersion B (Spec (.of K)) hK a :=
    MorphismProperty.RespectsIso.precomp _ G.toFunctor.reprW.hom G.ι hG.2
  have hda : DenseRange (Space.pointsMap B (Spec (.of K)) hK (yoneda.obj U) a) := by
    change Dense (Set.range (Space.pointsMap B (Spec (.of K)) hK
      (yoneda.obj G.toFunctor.reprX) (G.toFunctor.reprW.hom ≫ G.ι)))
    rw [Space.pointsMap_comp,
      (Space.pointsMap_surjective_of_isIso B (Spec (.of K)) hK
        G.toFunctor.reprW.hom).range_comp]
    exact hd
  exact ⟨U, a, ha, hda⟩

/-- The actual map from the SAME original representing scheme is a
literal dense open on all original tests. No original-map comparison is
supplied as a premise. -/
theorem originalChart_denseOpen
    (X : AlgebraicSpaces B (Spec (.of K)) hK)
    (U : BigFppfOver B (Spec (.of K)) hK) (a : yoneda.obj U ⟶ X.obj)
    (ha : Space.IsOpenImmersion B (Spec (.of K)) hK a)
    (hd : DenseRange (Space.pointsMap B (Spec (.of K)) hK (yoneda.obj U) a)) :
    M9StandaloneDraft.DenseOpen K (originalChart K B hK X U a) := by
  let f : schemeSpace U ⟶ X := ObjectProperty.homMk a
  have hf := AllTestNativeOriginalDenseOpen.denseOpen_of_native K B hK f ha hd
  apply AllTestDenseOpenTransport.denseOpen_of_iso K
    ((originalPresheafFunctor K B hK).map f) (originalChart K B hK X U a)
    (originalSchemeIso K B hK U) (Iso.refl _) _ hf
  simp [originalChart, f]

/-- The schematic locus yields a genuinely represented dense open, with
its native map and literal original map retained together. -/
theorem exists_original_dense_scheme
    (X : AlgebraicSpaces B (Spec (.of K)) hK)
    (hdec : Space.IsDecentSpace B (Spec (.of K)) hK X.obj) :
    ∃ (U : BigFppfOver B (Spec (.of K)) hK) (a : yoneda.obj U ⟶ X.obj),
      Space.IsOpenImmersion B (Spec (.of K)) hK a ∧
      DenseRange (Space.pointsMap B (Spec (.of K)) hK (yoneda.obj U) a) ∧
      M9StandaloneDraft.DenseOpen K (originalChart K B hK X U a) := by
  obtain ⟨U, a, ha, hd⟩ := exists_native_dense_scheme K B hK X hdec
  exact ⟨U, a, ha, hd, originalChart_denseOpen K B hK X U a ha hd⟩

/-- In the literal original language, native decency produces an actual
scheme over the original field and an actual represented dense-open map. -/
theorem exists_original_denseOpen
    (X : AlgebraicSpaces B (Spec (.of K)) hK)
    (hdec : Space.IsDecentSpace B (Spec (.of K)) hK X.obj) :
    ∃ (V : M9StandaloneDraft.Schemes K)
      (j : yoneda.obj V ⟶ (originalPresheafFunctor K B hK).obj X),
      M9StandaloneDraft.DenseOpen K j := by
  obtain ⟨U, a, _, _, hd⟩ := exists_original_dense_scheme K B hK X hdec
  exact ⟨(boundedInclusion B K hK).obj U, originalChart K B hK X U a, hd⟩

end M9StacksIntegration.NativeDenseSchematicOriginal
