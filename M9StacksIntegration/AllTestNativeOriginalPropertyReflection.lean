module

public import M9StacksIntegration.AllTestNativeOriginalPullbacks

/-! Actual original chart properties reflect to the same native arrow by
the proved represented pullback comparison and full faithfulness. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u
namespace M9StacksIntegration.AllTestNativeOriginalPropertyReflection
open AllTestBoundedCharts AllTestNativeOriginalFunctor AllTestNativeOriginalSchemes
  AllTestNativeOriginalPullbacks

variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- Given actual native representability, every literal original
represented scheme property reflects to the same native map. -/
theorem presheafProperty_of_original (P : MorphismProperty Scheme.{u})
    {X Y : AlgebraicSpaces B (Spec (.of K)) hK} (f : X ⟶ Y)
    (hr : yoneda.relativelyRepresentable f.hom)
    (hf : (P.inverseImage (Over.forget (M9StandaloneDraft.Base K))).presheaf
      ((originalPresheafFunctor K B hK).map f)) :
    (P.inverseImage (BigFppfOver.toScheme B (Spec (.of K)) hK)).presheaf f.hom := by
  refine ⟨hr, ?_⟩
  intro U V g a b h
  exact hf.property (originalChart K B hK Y U g)
    (originalChart K B hK X V a) ((boundedInclusion B K hK).map b)
    (originalChart_isPullback K B hK f a b g h)

/-- The actual native arrow recovered from any original chart whose
scheme belongs to the native site, using proved full faithfulness. -/
def nativeChartOfOriginal (X : AlgebraicSpaces B (Spec (.of K)) hK)
    (U : BigFppfOver B (Spec (.of K)) hK)
    (a : yoneda.obj ((boundedInclusion B K hK).obj U) ⟶
      (originalPresheafFunctor K B hK).obj X) : schemeSpace U ⟶ X :=
  (originalPresheafFullyFaithful K B hK).preimage
    ((originalSchemeIso K B hK U).hom ≫ a)

/-- Recovery preserves the literal entire-original-site chart arrow. -/
theorem nativeChartOfOriginal_map
    (X : AlgebraicSpaces B (Spec (.of K)) hK)
    (U : BigFppfOver B (Spec (.of K)) hK)
    (a : yoneda.obj ((boundedInclusion B K hK).obj U) ⟶
      (originalPresheafFunctor K B hK).obj X) :
    (originalPresheafFunctor K B hK).map (nativeChartOfOriginal K B hK X U a) =
      (originalSchemeIso K B hK U).hom ≫ a :=
  (originalPresheafFullyFaithful K B hK).map_preimage _

/-- No chosen native/original chart comparison is assumed: the recovered
native arrow has exactly the given original chart. -/
theorem originalChart_nativeChartOfOriginal
    (X : AlgebraicSpaces B (Spec (.of K)) hK)
    (U : BigFppfOver B (Spec (.of K)) hK)
    (a : yoneda.obj ((boundedInclusion B K hK).obj U) ⟶
      (originalPresheafFunctor K B hK).obj X) :
    originalChart K B hK X U (nativeChartOfOriginal K B hK X U a).hom = a := by
  change (originalSchemeIso K B hK U).inv ≫
    (originalPresheafFunctor K B hK).map (nativeChartOfOriginal K B hK X U a) = a
  rw [nativeChartOfOriginal_map]
  simp

/-- Every original represented chart property reflects to its actual
recovered native arrow. Native representability is derived from the
target's actual diagonal, rather than supplied as a premise. -/
theorem nativeChartOfOriginal_presheafProperty
    (P : MorphismProperty Scheme.{u})
    (X : AlgebraicSpaces B (Spec (.of K)) hK)
    (U : BigFppfOver B (Spec (.of K)) hK)
    (a : yoneda.obj ((boundedInclusion B K hK).obj U) ⟶
      (originalPresheafFunctor K B hK).obj X)
    (ha : (P.inverseImage (Over.forget (M9StandaloneDraft.Base K))).presheaf a) :
    (P.inverseImage (BigFppfOver.toScheme B (Spec (.of K)) hK)).presheaf
      (nativeChartOfOriginal K B hK X U a).hom := by
  let q := nativeChartOfOriginal K B hK X U a
  have ho : (P.inverseImage (Over.forget (M9StandaloneDraft.Base K))).presheaf
      ((originalPresheafFunctor K B hK).map q) := by
    let e : Arrow.mk ((originalPresheafFunctor K B hK).map q) ≅ Arrow.mk a :=
      Arrow.isoMk (originalSchemeIso K B hK U) (Iso.refl _) (by
        change (originalSchemeIso K B hK U).hom ≫ a =
          (originalPresheafFunctor K B hK).map q ≫ 𝟙 _
        simpa only [Category.comp_id, q] using
          (nativeChartOfOriginal_map K B hK X U a).symm)
    exact ((P.inverseImage (Over.forget (M9StandaloneDraft.Base K))).presheaf.arrow_mk_iso_iff
      e).mpr ha
  letI : HasBinaryProducts (BigFppfOver B (Spec (.of K)) hK) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  exact presheafProperty_of_original K B hK P q
    (X.property.diagonal_representable.of_diag q.hom) ho

end M9StacksIntegration.AllTestNativeOriginalPropertyReflection
