module

public import M9StacksIntegration.AllTestBoundedCharts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Continuous

/-!
# Restriction of the original all-test site to actual bounded sites

The full original test category is retained. The bounding site is chosen
separately for each test object; no one cutoff is asserted to contain every
scheme. The actual inclusion is continuous for fppf topologies. Its
restrictions detect equality and isomorphisms of the original natural maps.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.Functor

namespace M9StacksIntegration.AllTestBoundedRestriction
open AllTestBoundedCharts
universe u
variable (K : Type u) [Field K]

/-- A genuine native site can simultaneously contain the original field base
and any one original test scheme. There is no size assumption on the test. -/
theorem exists_site_contains_test (T : M9StandaloneDraft.Schemes K) :
    ∃ B : BigFppfSite.{u}, B.Contains (Spec (.of K)) ∧ B.Contains T.left := by
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing
    ({Spec (.of K), T.left} : Set Scheme.{u})
  exact ⟨B, hB _ (by simp), hB _ (by simp)⟩

variable (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K)))

/-- The explicit original-map inclusion is the native over-site inclusion. -/
theorem boundedInclusion_eq_post :
    boundedInclusion B K hK = Over.post (X := B.obj hK) B.inclusion := rfl

instance boundedInclusion_isContinuous :
    (boundedInclusion B K hK).IsContinuous (BigFppfOver.topology B (Spec (.of K)) hK)
      (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) := by
  rw [boundedInclusion_eq_post]
  exact BigFppfOver.isContinuous_post_inclusion B (Spec (.of K)) hK

abbrev restrict (F : M9StandaloneDraft.Presheaves K) :=
  (boundedInclusion B K hK).op ⋙ F

abbrev restrictMap {F G : M9StandaloneDraft.Presheaves K} (a : F ⟶ G) :
    restrict K B hK F ⟶ restrict K B hK G :=
  whiskerLeft (boundedInclusion B K hK).op a

/-- Restriction preserves the actual all-test fppf sheaf condition. -/
theorem restrict_isSheaf (F : M9StandaloneDraft.Presheaves K)
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) F) :
    Presheaf.IsSheaf (BigFppfOver.topology B (Spec (.of K)) hK) (restrict K B hK F) :=
  (boundedInclusion B K hK).op_comp_isSheaf_of_isSheaf _ _ F hF

/-- The literal restricted sheaf, with its values on the original schemes. -/
def restrictSheaf
    (F : Sheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) (Type u)) :
    Sheaf (BigFppfOver.topology B (Spec (.of K)) hK) (Type u) :=
  ⟨restrict K B hK F.obj, restrict_isSheaf K B hK F.obj F.property⟩

/-- The actual functor on sheaves uses the same component maps. -/
def restrictSheafFunctor :
    Sheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) (Type u) ⥤
      Sheaf (BigFppfOver.topology B (Spec (.of K)) hK) (Type u) where
  obj := restrictSheaf K B hK
  map a := ⟨restrictMap K B hK a.hom⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- All bounded restrictions together detect equality on the entire original
all-test category. The site may depend on the object being evaluated. -/
theorem hom_ext_of_bounded {F G : M9StandaloneDraft.Presheaves K} {a b : F ⟶ G}
    (h : ∀ (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K))),
      restrictMap K B hK a = restrictMap K B hK b) : a = b := by
  ext T x
  obtain ⟨B, hK, hT⟩ := exists_site_contains_test K T.unop
  let U := siteObject B (Spec (.of K)) hK hT T.unop.hom
  have he := NatTrans.congr_app (h B hK) (op U)
  change a.app (op ((boundedInclusion B K hK).obj U)) =
    b.app (op ((boundedInclusion B K hK).obj U)) at he
  rw [boundedInclusion_siteObject] at he
  exact ConcreteCategory.congr_hom he x

/-- A map of original all-test presheaves is an isomorphism if every bounded
restriction is. This proves an actual universe-compatible detection theorem. -/
theorem isIso_of_bounded {F G : M9StandaloneDraft.Presheaves K} (a : F ⟶ G)
    (h : ∀ (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K))),
      IsIso (restrictMap K B hK a)) : IsIso a := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro T
  obtain ⟨B, hK, hT⟩ := exists_site_contains_test K T.unop
  let U := siteObject B (Spec (.of K)) hK hT T.unop.hom
  letI := h B hK
  have hi : IsIso ((restrictMap K B hK a).app (op U)) := inferInstance
  change IsIso (a.app (op ((boundedInclusion B K hK).obj U))) at hi
  rw [boundedInclusion_siteObject] at hi
  exact hi

end M9StacksIntegration.AllTestBoundedRestriction
