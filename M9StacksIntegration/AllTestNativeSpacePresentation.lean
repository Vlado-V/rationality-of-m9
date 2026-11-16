module

public import M9StacksIntegration.AllTestLargeSiteAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCoverAtlas02WRb

/-!
# Actual original-site presentation of a native algebraic space

From the native algebraic-space axioms we take its genuine represented
surjective etale atlas and its genuine represented kernel pair. Universe
lift on their actual sections, followed by the proved sheaf extension,
gives a large-valued sheaf on the FULL original category with the SAME
original scheme presentation. No presentation premise is supplied.

Diagonal representability of the resulting full-site sheaf is a further
geometric step; this file does not declare the output an algebraic space.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestNativeSpacePresentation
open AllTestBoundedCharts AllTestLargeSitePullback AllTestLargeSiteAtlas
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- The genuine universe lift of a native sheaf. -/
def nativeLargeSheaf
    (A : Sheaf (BigFppfOver.topology B (Spec (.of K)) hK) (Type u)) :
    Sheaf (BigFppfOver.topology B (Spec (.of K)) hK) (Type (u+1)) :=
  (sheafCompose (BigFppfOver.topology B (Spec (.of K)) hK) uliftFunctor.{u+1, u}).obj A

/-- The literal universe lift of the actual native represented chart. -/
def nativeLargeAtlas
    (A : Sheaf (BigFppfOver.topology B (Spec (.of K)) hK) (Type u))
    (U : BigFppfOver B (Spec (.of K)) hK) (q : yoneda.obj U ⟶ A.obj) :
    (BigFppfOver.topology B (Spec (.of K)) hK).uliftYoneda.{u+1}.obj U ⟶
      nativeLargeSheaf K B hK A := ⟨Functor.whiskerRight q uliftFunctor.{u+1, u}⟩

/-- Actual local surjectivity survives the literal lift of sections. -/
theorem nativeLargeAtlas_isLocallySurjective
    (A : Sheaf (BigFppfOver.topology B (Spec (.of K)) hK) (Type u))
    (U : BigFppfOver B (Spec (.of K)) hK) (q : yoneda.obj U ⟶ A.obj)
    (hq : Presheaf.IsLocallySurjective (BigFppfOver.topology B (Spec (.of K)) hK) q) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B (Spec (.of K)) hK)
      (nativeLargeAtlas K B hK A U q).hom := by
  let : Presheaf.IsLocallySurjective (BigFppfOver.topology B (Spec (.of K)) hK) q := hq
  constructor
  intro X s
  refine (BigFppfOver.topology B (Spec (.of K)) hK).superset_covering ?_
    (Presheaf.imageSieve_mem _ q s.down)
  rintro Z g ⟨t, ht⟩
  exact ⟨ULift.up t, congrArg ULift.up ht⟩

/-- The actual represented kernel pair survives the universe lift. -/
theorem nativeLargeAtlas_isPullback
    (A : Sheaf (BigFppfOver.topology B (Spec (.of K)) hK) (Type u))
    {U R : BigFppfOver B (Spec (.of K)) hK} (s t : R ⟶ U)
    (q : yoneda.obj U ⟶ A.obj)
    (h : IsPullback (yoneda.map s) (yoneda.map t) q q) :
    IsPullback
      ((BigFppfOver.topology B (Spec (.of K)) hK).uliftYoneda.{u+1}.map s)
      ((BigFppfOver.topology B (Spec (.of K)) hK).uliftYoneda.{u+1}.map t)
      (nativeLargeAtlas K B hK A U q) (nativeLargeAtlas K B hK A U q) := by
  apply IsPullback.of_map_of_faithful
    (F := sheafToPresheaf (BigFppfOver.topology B (Spec (.of K)) hK) (Type (u+1)))
  exact h.map ((Functor.whiskeringRight _ _ _).obj uliftFunctor.{u+1, u})

/-- The actual large-valued extension of a native algebraic-space sheaf. -/
def extendedNativeSheaf
    (F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B (Spec (.of K)) hK F) :
    Sheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) (Type (u+1)) :=
  (extendSheaf K B hK).obj (nativeLargeSheaf K B hK ⟨F, hF.isSheaf⟩)

/-- EVERY actual native algebraic space extends to a full-original-site
sheaf with an actual locally surjective original atlas and its actual same
represented kernel pair. Both relation projections remain surjective etale. -/
theorem exists_extended_native_presentation
    (F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B (Spec (.of K)) hK F) :
    ∃ (U R : BigFppfOver B (Spec (.of K)) hK) (s t : R ⟶ U)
      (a : uliftYoneda.{u+1}.obj ((boundedInclusion B K hK).obj U) ⟶
        (extendedNativeSheaf K B hK F hF).obj),
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) a ∧
      IsPullback (uliftYoneda.{u+1}.map ((boundedInclusion B K hK).map s))
        (uliftYoneda.{u+1}.map ((boundedInclusion B K hK).map t)) a a ∧
      Surjective ((BigFppfOver.toScheme B (Spec (.of K)) hK).map s) ∧
      Etale ((BigFppfOver.toScheme B (Spec (.of K)) hK).map s) ∧
      Surjective ((BigFppfOver.toScheme B (Spec (.of K)) hK).map t) ∧
      Etale ((BigFppfOver.toScheme B (Spec (.of K)) hK).map t) := by
  obtain ⟨U, q, hqs, hqe⟩ := hF.exists_atlas
  let R := hqe.rep.pullback q
  let s : R ⟶ U := hqe.rep.fst' q
  let t : R ⟶ U := hqe.rep.snd q
  have hR : IsPullback (yoneda.map s) (yoneda.map t) q q := hqe.rep.isPullback' q
  let A : Sheaf (BigFppfOver.topology B (Spec (.of K)) hK) (Type u) := ⟨F, hF.isSheaf⟩
  let Q := nativeLargeAtlas K B hK A U q
  have hls : Presheaf.IsLocallySurjective (BigFppfOver.topology B (Spec (.of K)) hK) q :=
    Space.isLocallySurjective_of_presheaf_surjective_etale B (Spec (.of K)) hK
      (G := A) (a := q) hqs hqe
  refine ⟨U, R, s, t, (extendedAtlas K B hK _ U Q).hom,
    extendedAtlas_isLocallySurjective K B hK _ U Q
      (nativeLargeAtlas_isLocallySurjective K B hK A U q hls),
    extendedAtlas_presheaf_isPullback K B hK _ s t Q
      (nativeLargeAtlas_isPullback K B hK A s t q hR), ?_, ?_, ?_, ?_⟩
  · exact hqs.property q (yoneda.map t) s hR.flip
  · exact hqe.property q (yoneda.map t) s hR.flip
  · exact hqs.property q (yoneda.map s) t hR
  · exact hqe.property q (yoneda.map s) t hR

end M9StacksIntegration.AllTestNativeSpacePresentation
