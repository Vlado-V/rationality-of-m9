module

public import M9StacksIntegration.AllTestBoundedRepresentability
public import M9StacksIntegration.AllTestBoundedAtlas
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# The actual native algebraic space of a restricted original family

The diagonal is represented by original pullbacks, whose boundedness follows
from the proved size theorem for arbitrary monomorphisms. The atlas is the
actual restricted single schematic chart, already checked after every
represented base change. Thus no algebraicity, classification or family
comparison premise is supplied.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestBoundedAlgebraicSpace
open AllTestBoundedCharts AllTestBoundedRestriction AllTestBoundedRepresentability
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

abbrev restrictionFunctor : M9StandaloneDraft.Presheaves K ⥤
    ((BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u) :=
  (Functor.whiskeringLeft _ _ _).obj (boundedInclusion B K hK).op

/-- The restriction of an original representable diagonal remains an actual
representable diagonal. Arbitrary monomorphisms satisfy the needed cutoff
bound, so no extra finiteness property of the original diagonal is assumed. -/
theorem diagonal_restrict (F : M9StandaloneDraft.Presheaves K)
    (hF : yoneda.relativelyRepresentable (diag F)) :
    yoneda.relativelyRepresentable (diag (restrict K B hK F)) := by
  let L := restrictionFunctor K B hK
  have hd : yoneda.relativelyRepresentable (L.map (diag F)) :=
    restrict_relativelyRepresentable_of_mono K B hK (diag F) hF
  have he : diag (L.obj F) = L.map (diag F) ≫ prodComparison L F F := by
    apply prod.hom_ext <;> simp only [Category.assoc, prodComparison_fst,
      prodComparison_snd, ← L.map_comp, prod.lift_fst, prod.lift_snd, L.map_id]
  change yoneda.relativelyRepresentable (diag (L.obj F))
  rw [he, (yoneda.relativelyRepresentable).cancel_right_of_respectsIso]
  exact hd

/-- Restricting EVERY original all-test family over a bounded test base gives
a genuine native algebraic space over the original field. This is proved
from the original geometric definitions; no native algebraicity, classifier
or equivalence of families is assumed. -/
theorem isAlgebraicSpace_restrict_family
    {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    IsAlgebraicSpace B (Spec (.of K)) hK (restrict K B hK F.total.obj) :=
  ⟨restrict_isSheaf K B hK F.total.obj F.total.isSheaf,
    diagonal_restrict K B hK F.total.obj F.total.diagonal,
    AllTestBoundedAtlas.exists_restricted_etale_atlas K B hK F⟩

/-- The actual native algebraic space retains the restricted original total
presheaf literally. -/
def restrictedFamilySpace
    {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    AlgebraicSpaces B (Spec (.of K)) hK :=
  ⟨restrict K B hK F.total.obj, isAlgebraicSpace_restrict_family K B hK F⟩

@[simp] theorem restrictedFamilySpace_obj
    {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    (restrictedFamilySpace K B hK F).obj = restrict K B hK F.total.obj := rfl

end M9StacksIntegration.AllTestBoundedAlgebraicSpace
