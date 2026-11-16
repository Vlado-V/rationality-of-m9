module

public import M9StacksIntegration.PresheafValuedClassifierReflection
public import M9StacksIntegration.SchemeValuedClassifierReflection
public import M9StacksIntegration.AllTestNativeOriginalSchemes

/-! Actual algebraic-space-valued classifiers and physical scheme restrictions.
The target is a genuine native algebraic space. Classifier transformations
force equal actual maps; a genuine monomorphism and actual pullback squares
then force equality of the restricted scheme maps on every original test. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.AlgebraicSpaceValuedClassifierReflection

universe u uD vD

section Native
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The ACTUAL category fibred in groupoids of the given algebraic space. -/
abbrev target (M : AlgebraicSpaces B S hS) := (Stack.fibredCategory B S hS M.obj).val

variable {D : Type uD} [Category.{vD} D] {p : D ⥤ BigFppfOver B S hS}
  {M : AlgebraicSpaces B S hS}
  (κ : BasedCategory.ofFunctor p ⥤ᵇ target B S hS M)
  {U V : BigFppfOver B S hS}

/-- The genuine scheme-space map given by the classifier and the given
algebraic-space-valued morphism. No invariance is imposed on κ. -/
def nativeMap (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p) :
    schemeSpace U ⟶ M :=
  ObjectProperty.homMk (PresheafValuedClassifierReflection.representingMap (BasedFunctor.comp F κ))

/-- Actual classifier transformations force literal algebraic-space maps equal. -/
theorem nativeMap_eq
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p}
    (η : F ⟶ G) : nativeMap B S hS κ F = nativeMap B S hS κ G :=
  ObjectProperty.hom_ext _
    (PresheafValuedClassifierReflection.representingMap_eq_of_transformation (BasedCategory.whiskerRight η κ))

/-- The actual map commutes with actual base precomposition. -/
theorem nativeMap_precompose
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p) (a : V ⟶ U) :
    nativeMap B S hS κ (BasedFunctor.comp (PresheafValuedClassifierReflection.sliceMap a) F) =
      schemeSpaceMap a ≫ nativeMap B S hS κ F := by
  apply ObjectProperty.hom_ext
  exact PresheafValuedClassifierReflection.representingMap_precompose (BasedFunctor.comp F κ) a

private theorem schemeMap_comp {A B' C : BigFppfOver B S hS}
    (a : A ⟶ B') (b : B' ⟶ C) :
    schemeSpaceMap (a ≫ b) = schemeSpaceMap a ≫ schemeSpaceMap b :=
  (schemeSpaceFunctor B S hS).map_comp a b

/-- Cancel the genuine represented open (or any actual monomorphism).
Only its physical factorization triangles are inputs; classifier
invariance is DERIVED from η. -/
theorem restriction_eq
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p}
    (j : schemeSpace V ⟶ M) [Mono j] (r s : U ⟶ V)
    (hr : schemeSpaceMap r ≫ j = nativeMap B S hS κ F)
    (hs : schemeSpaceMap s ≫ j = nativeMap B S hS κ G) (η : F ⟶ G) : r = s := by
  have he : schemeSpaceMap r = schemeSpaceMap s := by
    apply (cancel_mono j).mp
    rw [hr, hs]
    exact nativeMap_eq B S hS κ η
  apply yoneda.map_injective
  exact congrArg (fun f : schemeSpace U ⟶ schemeSpace V => f.hom) he

/-- Real pullback squares describe the two inverse-image schemes. Their
maps agree on any actual common domain carrying a classifier transformation. -/
theorem cartesian_restriction_eq
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p}
    (j : schemeSpace V ⟶ M) [Mono j]
    {W₀ W₁ T : BigFppfOver B S hS} (π₀ : W₀ ⟶ U) (π₁ : W₁ ⟶ U)
    (r₀ : W₀ ⟶ V) (r₁ : W₁ ⟶ V)
    (h₀ : IsPullback (schemeSpaceMap r₀) (schemeSpaceMap π₀) j (nativeMap B S hS κ F))
    (h₁ : IsPullback (schemeSpaceMap r₁) (schemeSpaceMap π₁) j (nativeMap B S hS κ G))
    (a : T ⟶ W₀) (b : T ⟶ W₁)
    (η : BasedFunctor.comp (PresheafValuedClassifierReflection.sliceMap (a ≫ π₀)) F ⟶
      BasedFunctor.comp (PresheafValuedClassifierReflection.sliceMap (b ≫ π₁)) G) : a ≫ r₀ = b ≫ r₁ := by
  refine restriction_eq B S hS κ j (a ≫ r₀) (b ≫ r₁) ?_ ?_ η
  · rw [nativeMap_precompose]
    simp only [schemeMap_comp, Category.assoc]
    rw [h₀.w]
  · rw [nativeMap_precompose]
    simp only [schemeMap_comp, Category.assoc]
    rw [h₁.w]

/-- The restriction is equality of the SAME original scheme morphisms. -/
theorem restriction_schemeMap_eq
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p}
    (j : schemeSpace V ⟶ M) [Mono j] (r s : U ⟶ V)
    (hr : schemeSpaceMap r ≫ j = nativeMap B S hS κ F)
    (hs : schemeSpaceMap s ≫ j = nativeMap B S hS κ G) (η : F ⟶ G) :
    (BigFppfOver.toScheme B S hS).map r = (BigFppfOver.toScheme B S hS).map s :=
  congrArg (BigFppfOver.toScheme B S hS).map (restriction_eq B S hS κ j r s hr hs η)

/-- Every ORIGINAL test pulls back the genuine common-domain equality.
There is no bounded-site membership hypothesis on Z. -/
theorem cartesian_restriction_all_original_tests
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p}
    (j : schemeSpace V ⟶ M) [Mono j]
    {W₀ W₁ T : BigFppfOver B S hS} (π₀ : W₀ ⟶ U) (π₁ : W₁ ⟶ U)
    (r₀ : W₀ ⟶ V) (r₁ : W₁ ⟶ V)
    (h₀ : IsPullback (schemeSpaceMap r₀) (schemeSpaceMap π₀) j (nativeMap B S hS κ F))
    (h₁ : IsPullback (schemeSpaceMap r₁) (schemeSpaceMap π₁) j (nativeMap B S hS κ G))
    (a : T ⟶ W₀) (b : T ⟶ W₁)
    (η : BasedFunctor.comp (PresheafValuedClassifierReflection.sliceMap (a ≫ π₀)) F ⟶
      BasedFunctor.comp (PresheafValuedClassifierReflection.sliceMap (b ≫ π₁)) G)
    (Z : Scheme.{u}) (z : Z ⟶ (BigFppfOver.toScheme B S hS).obj T) :
    z ≫ (BigFppfOver.toScheme B S hS).map (a ≫ r₀) =
      z ≫ (BigFppfOver.toScheme B S hS).map (b ≫ r₁) :=
  congrArg (fun f => z ≫ (BigFppfOver.toScheme B S hS).map f)
    (cartesian_restriction_eq B S hS κ j π₀ π₁ r₀ r₁ h₀ h₁ a b η)

end Native

section Original
open M9StacksIntegration.AllTestNativeOriginalFunctor
open M9StacksIntegration.AllTestNativeOriginalSchemes
open M9StacksIntegration.AllTestBoundedCharts

variable (K : Type u) [Field K] (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K)))
  {D : Type uD} [Category.{vD} D] {p : D ⥤ BigFppfOver B (Spec (.of K)) hK}
  {M : AlgebraicSpaces B (Spec (.of K)) hK}
  (κ : BasedCategory.ofFunctor p ⥤ᵇ target B (Spec (.of K)) hK M)
  {U V : BigFppfOver B (Spec (.of K)) hK}

/-- The SAME actual algebraic-space map on the FULL original site, with
its source identified with the literal original represented scheme. -/
def originalMap
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p) :
    yoneda.obj ((boundedInclusion B K hK).obj U) ⟶ (originalPresheafFunctor K B hK).obj M :=
  (originalSchemeIso K B hK U).inv ≫
    (originalPresheafFunctor K B hK).map (nativeMap B (Spec (.of K)) hK κ F)

theorem originalMap_eq
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p}
    (η : F ⟶ G) : originalMap K B hK κ F = originalMap K B hK κ G :=
  congrArg (fun f => (originalSchemeIso K B hK U).inv ≫
    (originalPresheafFunctor K B hK).map f) (nativeMap_eq B (Spec (.of K)) hK κ η)

/-- A genuine represented original open may be outside the bounded site.
Its monomorphism still cancels on actual original scheme maps. -/
theorem original_restriction_eq
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p}
    (η : F ⟶ G) (V₀ : M9StandaloneDraft.Schemes K)
    (j : yoneda.obj V₀ ⟶ (originalPresheafFunctor K B hK).obj M) [Mono j]
    (W : M9StandaloneDraft.Schemes K)
    (a : W ⟶ (boundedInclusion B K hK).obj U) (r s : W ⟶ V₀)
    (hr : yoneda.map r ≫ j = yoneda.map a ≫ originalMap K B hK κ F)
    (hs : yoneda.map s ≫ j = yoneda.map a ≫ originalMap K B hK κ G) : r = s := by
  apply yoneda.map_injective
  apply (cancel_mono j).mp
  rw [hr, hs, originalMap_eq K B hK κ η]

/-- Physical ORIGINAL inverse-image schemes have equal restricted maps on
any actual common domain. None of V₀,W₀,W₁,Z is assumed to belong to B. -/
theorem original_cartesian_restriction_eq
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p}
    (η : F ⟶ G) (V₀ : M9StandaloneDraft.Schemes K)
    (j : yoneda.obj V₀ ⟶ (originalPresheafFunctor K B hK).obj M) [Mono j]
    {W₀ W₁ Z : M9StandaloneDraft.Schemes K}
    (π₀ : W₀ ⟶ (boundedInclusion B K hK).obj U)
    (π₁ : W₁ ⟶ (boundedInclusion B K hK).obj U) (r₀ : W₀ ⟶ V₀) (r₁ : W₁ ⟶ V₀)
    (h₀ : IsPullback (yoneda.map r₀) (yoneda.map π₀) j (originalMap K B hK κ F))
    (h₁ : IsPullback (yoneda.map r₁) (yoneda.map π₁) j (originalMap K B hK κ G))
    (a : Z ⟶ W₀) (b : Z ⟶ W₁) (hbase : a ≫ π₀ = b ≫ π₁) : a ≫ r₀ = b ≫ r₁ := by
  refine original_restriction_eq K B hK κ η V₀ j Z (a ≫ π₀) (a ≫ r₀) (b ≫ r₁) ?_ ?_
  · simp only [Functor.map_comp, Category.assoc]
    rw [h₀.w]
  · rw [hbase]
    simp only [Functor.map_comp, Category.assoc]
    rw [h₁.w]

/-- Values agree at EVERY original test, including tests outside B. -/
theorem originalMap_app_eq
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p}
    (η : F ⟶ G) (T : M9StandaloneDraft.Schemes K)
    (x : T ⟶ (boundedInclusion B K hK).obj U) :
    (originalMap K B hK κ F).app (op T) x = (originalMap K B hK κ G).app (op T) x :=
  congrArg (fun f => f.app (op T) x) (originalMap_eq K B hK κ η)

/-- Native precomposition remains the literal original Yoneda precomposition. -/
theorem originalMap_precompose
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor p) (a : V ⟶ U) :
    originalMap K B hK κ (BasedFunctor.comp (PresheafValuedClassifierReflection.sliceMap a) F) =
      yoneda.map ((boundedInclusion B K hK).map a) ≫ originalMap K B hK κ F := by
  have he : (originalSchemeIso K B hK V).inv ≫
      (originalPresheafFunctor K B hK).map (schemeSpaceMap a) =
        yoneda.map ((boundedInclusion B K hK).map a) ≫ (originalSchemeIso K B hK U).inv := by
    calc
      (originalSchemeIso K B hK V).inv ≫
          (originalPresheafFunctor K B hK).map (schemeSpaceMap a) =
          ((originalSchemeIso K B hK V).inv ≫
            ((originalPresheafFunctor K B hK).map (schemeSpaceMap a) ≫
              (originalSchemeIso K B hK U).hom)) ≫ (originalSchemeIso K B hK U).inv := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = ((originalSchemeIso K B hK V).inv ≫
          ((originalSchemeIso K B hK V).hom ≫
            yoneda.map ((boundedInclusion B K hK).map a))) ≫
              (originalSchemeIso K B hK U).inv := by
        rw [originalSchemeIso_naturality K B hK a]
      _ = _ := by rw [Iso.inv_hom_id_assoc]
  dsimp only [originalMap]
  rw [nativeMap_precompose, Functor.map_comp, ← Category.assoc, he, Category.assoc]

end Original
end M9Native.AlgebraicSpaceValuedClassifierReflection
