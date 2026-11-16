module

public import M9StacksIntegration.NativeSmoothGenusCoarseClassifier
public import M9StacksIntegration.AllOriginalCoarseClassifierFibre

/-! The actual chosen native field coarse map and its original point values.
The same chosen coarseMap is used throughout. Its proved universal
homeomorphism supplies the simultaneous original-field source-arrow result;
no universal-homeomorphism or original-field site-bound premise is input. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Opposite
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.NativeSmoothGenusCoarseMap
open M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AllTestNativeOriginalFunctor
  M9StacksIntegration.AllTestNativeOriginalPullbacks

universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (g : ℕ) (hg : 2 ≤ g)

/-- The actual classifier composed with the EXACT chosen native coarse map. -/
def nativeMap {U : BigFppfOver B (Spec (.of K)) hK}
    (A : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val) :
    schemeSpace U ⟶ M9StacksIntegration.GenusNineCoarseOverField.coarseSpace B hZ K hK g hg :=
  ASClassifierGeometricLift.nativeMap B (Spec (.of K)) hK
    (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ K hK g hg) A

/-- The same native map on the original all-test presheaf, from the SAME
original parameter scheme with its original coefficient map. -/
def originalChart {U : BigFppfOver B (Spec (.of K)) hK}
    (A : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val) :
    yoneda.obj ((boundedInclusion B K hK).obj U) ⟶
      (originalPresheafFunctor K B hK).obj
        (M9StacksIntegration.GenusNineCoarseOverField.coarseSpace B hZ K hK g hg) :=
  M9StacksIntegration.AllTestNativeOriginalPullbacks.originalChart K B hK
    (M9StacksIntegration.GenusNineCoarseOverField.coarseSpace B hZ K hK g hg) U
    (nativeMap B hZ K hK g hg A).hom

/-- Actual values over EVERY original coefficient-field extension.
No containment of the original test field in B is required. -/
def pointValue {U : BigFppfOver B (Spec (.of K)) hK}
    (A : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val)
    (L : Type u) [Field L] [Algebra K L]
    (x : M9StandaloneDraft.FieldPoint K L ⟶ (boundedInclusion B K hK).obj U) :
    ((originalPresheafFunctor K B hK).obj
      (M9StacksIntegration.GenusNineCoarseOverField.coarseSpace B hZ K hK g hg)).obj
        (op (M9StandaloneDraft.FieldPoint K L)) :=
  (originalChart B hZ K hK g hg A).app (op (M9StandaloneDraft.FieldPoint K L)) x

/-- Precomposition retains the literal chosen native coarse map. -/
theorem nativeMap_precompose {U T : BigFppfOver B (Spec (.of K)) hK}
    (A : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val)
    (a : T ⟶ U) :
    nativeMap B hZ K hK g hg
        (BasedFunctor.comp (PresheafValuedClassifierReflection.sliceMap a) A) =
      schemeSpaceMap a ≫ nativeMap B hZ K hK g hg A :=
  AllOriginalCoarseClassifierFibre.nativeMap_precompose K B hK
    (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ K hK g hg) A a

/-- The actual schematic classifying map to the exact chosen field coarse
space; schematic membership is supplied by the proved original curve predicate. -/
def classifyingMap (T : BigFppfOver B (Spec (.of K)) hK)
    {Z : BigFppfOver B integerBase hZ}
    (q : Z ⟶ (Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj T)
    (hq : M9StandaloneDraft.SchemeCurve
      ((BigFppfOver.toScheme B integerBase hZ).map q) g) :
    schemeSpace T ⟶ M9StacksIntegration.GenusNineCoarseOverField.coarseSpace B hZ K hK g hg :=
  nativeMap B hZ K hK g hg
    (NativeSmoothGenusCoarseClassifier.classifyingMor B hZ K hK T q g hg hq)

/-- Equal actual original coarse values give an actual chosen-source
arrow over the identity of one simultaneous bounded ACL field. The genuine
UH of the chosen coarseMap is DERIVED, as are both recovered original maps. -/
theorem exists_simultaneous_source_arrow
    (U V : BigFppfOver B (Spec (.of K)) hK)
    (A : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val)
    (D : BasedCategory.ofFunctor (Over.forget V) ⥤ᵇ
      (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val)
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L]
    (x : M9StandaloneDraft.FieldPoint K L ⟶ (boundedInclusion B K hK).obj U)
    (y : M9StandaloneDraft.FieldPoint K L ⟶ (boundedInclusion B K hK).obj V)
    (hxy : pointValue B hZ K hK g hg A L x = pointValue B hZ K hK g hg D L y) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (hΩ : B.Contains (Spec (.of Ω))) (sΩ : Spec (.of Ω) ⟶ Spec (.of K))
      (a : siteObject B (Spec (.of K)) hK hΩ sΩ ⟶ U)
      (b : siteObject B (Spec (.of K)) hK hΩ sΩ ⟶ V)
      (v : M9StandaloneDraft.FieldPoint K L ⟶
        (boundedInclusion B K hK).obj (siteObject B (Spec (.of K)) hK hΩ sΩ))
      (α : (BasedFunctor.comp (PresheafValuedClassifierReflection.sliceMap a) A).toFunctor.obj
          (Functor.FiberedMor.unit (siteObject B (Spec (.of K)) hK hΩ sΩ)) ⟶
        (BasedFunctor.comp (PresheafValuedClassifierReflection.sliceMap b) D).toFunctor.obj
          (Functor.FiberedMor.unit (siteObject B (Spec (.of K)) hK hΩ sΩ))),
      (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.p.IsHomLift
        (𝟙 (siteObject B (Spec (.of K)) hK hΩ sΩ)) α ∧
      v ≫ (boundedInclusion B K hK).map a = x ∧
      v ≫ (boundedInclusion B K hK).map b = y :=
  AllOriginalCoarseClassifierFibre.exists_simultaneous_source_arrow K B hK
    (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ K hK g hg)
    (M9StacksIntegration.GenusNineCoarseOverField.coarseMap_universalHomeomorphism B hZ K hK g hg)
    U V A D L x y hxy

end M9Native.NativeSmoothGenusCoarseMap
