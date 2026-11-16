module

public import M9StacksIntegration.AllTestBoundedFull
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Recovering original represented subobjects from actual bounded descent

The chart-lifting map is literal Yoneda evaluation at the same original
scheme. For a monomorphism from a bounded represented scheme, an actual
bounded isomorphism and an actual bounded locally surjective original
chart imply an isomorphism on EVERY original test. This is proved from
sections and the actual covering chart; no fully-faithful or all-test
classification assumption is used.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestBoundedMonoRepresentability
open AllTestBoundedCharts AllTestBoundedRestriction AllTestBoundedCartesian
  AllTestBoundedFull AllTestBoundedAlgebraicSpace
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- An actual map from a native represented source lifts by literal evaluation. -/
def liftChartMap {A : M9StandaloneDraft.Presheaves K}
    (Z : BigFppfOver B (Spec (.of K)) hK)
    (b : yoneda.obj Z ⟶ restrict K B hK A) :
    yoneda.obj ((boundedInclusion B K hK).obj Z) ⟶ A :=
  yonedaEquiv.symm (b.app (op Z) (𝟙 Z))

/-- Restriction of that actual original map is exactly the input map. -/
theorem chartMap_liftChartMap {A : M9StandaloneDraft.Presheaves K}
    (Z : BigFppfOver B (Spec (.of K)) hK)
    (b : yoneda.obj Z ⟶ restrict K B hK A) :
    chartMap K B hK Z (liftChartMap K B hK Z b) = b := by
  apply yonedaEquiv.injective
  change (liftChartMap K B hK Z b).app
      (op ((boundedInclusion B K hK).obj Z))
      ((boundedInclusion B K hK).map (𝟙 Z)) = yonedaEquiv b
  rw [(boundedInclusion B K hK).map_id]
  change A.map (𝟙 _) (b.app (op Z) (𝟙 Z)) = b.app (op Z) (𝟙 Z)
  rw [A.map_id]
  rfl

/-- Literal represented scheme maps commute with the chart/base comparison. -/
theorem chartMap_yoneda_map
    {Z T : BigFppfOver B (Spec (.of K)) hK} (p : Z ⟶ T) :
    chartMap K B hK Z (yoneda.map ((boundedInclusion B K hK).map p)) ≫
      (restrictRepresentableIso B K hK T).hom = yoneda.map p := by
  dsimp only [chartMap]
  rw [Category.assoc, restrictRepresentableIso_naturality, Iso.inv_hom_id_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A native isomorphism from an original represented subobject is an
all-test isomorphism once an actual bounded original chart covers it. -/
theorem isIso_of_chartMap_isIso_of_mono
    {A : M9StandaloneDraft.Presheaves K}
    (hA : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) A)
    (Z : BigFppfOver B (Spec (.of K)) hK)
    (b : yoneda.obj ((boundedInclusion B K hK).obj Z) ⟶ A)
    [Mono b] [IsIso (chartMap K B hK Z b)]
    (R : BigFppfOver B (Spec (.of K)) hK)
    (a : yoneda.obj ((boundedInclusion B K hK).obj R) ⟶ A)
    (ha : Presheaf.IsLocallySurjective
      (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) a) : IsIso b := by
  let c : R ⟶ Z := yoneda.preimage
    (chartMap K B hK R a ≫ inv (chartMap K B hK Z b))
  have hc : yoneda.map ((boundedInclusion B K hK).map c) ≫ b = a := by
    apply chartMap_injective K B hK R
    rw [chartMap_comp_yoneda]
    change yoneda.map c ≫ chartMap K B hK Z b = _
    rw [show yoneda.map c =
      chartMap K B hK R a ≫ inv (chartMap K B hK Z b) from yoneda.map_preimage _]
    simp
  let : Presheaf.IsLocallySurjective
      (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) a := ha
  let : Presheaf.IsLocallySurjective
      (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) b :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ hc
  let YZ : Sheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) (Type u) :=
    (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)).yoneda.obj
      ((boundedInclusion B K hK).obj Z)
  let bS : YZ ⟶ (⟨A, hA⟩ : Sheaf
      (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) (Type u)) := ⟨b⟩
  have hi : Presheaf.IsLocallyInjective
      (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) b :=
    Presheaf.isLocallyInjective_of_injective _ b (fun T =>
      (CategoryTheory.mono_iff_injective (b.app T)).mp inferInstance)
  let : IsIso bS := (Sheaf.isLocallyBijective_iff_isIso bS).mp ⟨hi, inferInstance⟩
  exact inferInstanceAs (IsIso ((sheafToPresheaf _ _).map bS))

end M9StacksIntegration.AllTestBoundedMonoRepresentability
