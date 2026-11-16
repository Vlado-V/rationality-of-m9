module

public import M9StacksIntegration.AllTestLargeSiteYoneda
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Actual atlas and kernel-pair transport to the original site

The constructed sheaf extension sends a genuine locally surjective native
represented chart to a locally surjective chart from the SAME original
scheme. Its actual represented kernel pair is the same pair of original
scheme maps. Surjectivity follows from preservation of epimorphisms by the
actual left adjoint; the kernel pair follows from proved left exactness.
No diagonal-representability or effective-descent premise is introduced.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestLargeSiteAtlas
open AllTestBoundedCharts AllTestLargeSitePullback AllTestLargeSiteYoneda
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- The actual extended atlas on every original test scheme. -/
def extendedAtlas
    (A : Sheaf (BigFppfOver.topology B (Spec (.of K)) hK) (Type (u+1)))
    (U : BigFppfOver B (Spec (.of K)) hK)
    (q : (BigFppfOver.topology B (Spec (.of K)) hK).uliftYoneda.{u+1}.obj U ⟶ A) :
    (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)).uliftYoneda.{u+1}.obj
        ((boundedInclusion B K hK).obj U) ⟶ (extendSheaf K B hK).obj A :=
  ((extendCompYonedaIso K B hK).app U).inv ≫ (extendSheaf K B hK).map q

/-- Local surjectivity is a conclusion about the actual full original site. -/
theorem extendedAtlas_isLocallySurjective
    (A : Sheaf (BigFppfOver.topology B (Spec (.of K)) hK) (Type (u+1)))
    (U : BigFppfOver B (Spec (.of K)) hK)
    (q : (BigFppfOver.topology B (Spec (.of K)) hK).uliftYoneda.{u+1}.obj U ⟶ A)
    (hq : Presheaf.IsLocallySurjective
      (BigFppfOver.topology B (Spec (.of K)) hK) q.hom) :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (M9StandaloneDraft.Base K))
      (extendedAtlas K B hK A U q).hom := by
  let : Sheaf.IsLocallySurjective q := hq
  let : Epi q := (Sheaf.isLocallySurjective_iff_epi q).mp hq
  let : PreservesColimits (extendSheaf K B hK) :=
    (extendSheafAdjunction K B hK).leftAdjoint_preservesColimits
  exact (Sheaf.isLocallySurjective_iff_epi (extendedAtlas K B hK A U q)).mpr
    (inferInstanceAs (Epi
      (((extendCompYonedaIso K B hK).app U).inv ≫ (extendSheaf K B hK).map q)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual kernel-pair square transports with its literal scheme maps. -/
theorem extendedAtlas_isPullback
    (A : Sheaf (BigFppfOver.topology B (Spec (.of K)) hK) (Type (u+1)))
    {U R : BigFppfOver B (Spec (.of K)) hK} (s t : R ⟶ U)
    (q : (BigFppfOver.topology B (Spec (.of K)) hK).uliftYoneda.{u+1}.obj U ⟶ A)
    (h : IsPullback
      ((BigFppfOver.topology B (Spec (.of K)) hK).uliftYoneda.{u+1}.map s)
      ((BigFppfOver.topology B (Spec (.of K)) hK).uliftYoneda.{u+1}.map t) q q) :
    IsPullback
      ((Scheme.fppfTopology.over (M9StandaloneDraft.Base K)).uliftYoneda.{u+1}.map
        ((boundedInclusion B K hK).map s))
      ((Scheme.fppfTopology.over (M9StandaloneDraft.Base K)).uliftYoneda.{u+1}.map
        ((boundedInclusion B K hK).map t))
      (extendedAtlas K B hK A U q) (extendedAtlas K B hK A U q) := by
  let : PreservesFiniteLimits (extendSheaf K B hK) :=
    extendSheaf_preservesFiniteLimits K B hK
  let e := extendCompYonedaIso K B hK
  apply (h.map (extendSheaf K B hK)).of_iso
    (e.app R) (e.app U) (e.app U) (Iso.refl _)
  · exact e.hom.naturality s
  · exact e.hom.naturality t
  · simp only [Iso.refl_hom, Category.comp_id, extendedAtlas, e, Iso.hom_inv_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, extendedAtlas, e, Iso.hom_inv_id_assoc]

/-- The same kernel pair in actual presheaves on ALL original tests. -/
theorem extendedAtlas_presheaf_isPullback
    (A : Sheaf (BigFppfOver.topology B (Spec (.of K)) hK) (Type (u+1)))
    {U R : BigFppfOver B (Spec (.of K)) hK} (s t : R ⟶ U)
    (q : (BigFppfOver.topology B (Spec (.of K)) hK).uliftYoneda.{u+1}.obj U ⟶ A)
    (h : IsPullback
      ((BigFppfOver.topology B (Spec (.of K)) hK).uliftYoneda.{u+1}.map s)
      ((BigFppfOver.topology B (Spec (.of K)) hK).uliftYoneda.{u+1}.map t) q q) :
    IsPullback
      (uliftYoneda.{u+1}.map ((boundedInclusion B K hK).map s))
      (uliftYoneda.{u+1}.map ((boundedInclusion B K hK).map t))
      (extendedAtlas K B hK A U q).hom (extendedAtlas K B hK A U q).hom :=
  (extendedAtlas_isPullback K B hK A s t q h).map
    (sheafToPresheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) (Type (u+1)))

end M9StacksIntegration.AllTestLargeSiteAtlas
