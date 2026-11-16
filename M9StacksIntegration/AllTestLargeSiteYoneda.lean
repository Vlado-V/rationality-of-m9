module

public import M9StacksIntegration.AllTestLargeSitePullback
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical
public import Mathlib.CategoryTheory.Sites.Subcanonical

/-!
# The sheaf extension carries the same schemes and scheme maps

The adjunction and the actual sheaf Yoneda equivalence identify the inverse
image of a native represented sheaf with the represented sheaf of the same
ORIGINAL scheme. The identification is natural in the scheme map. This is
an actual isomorphism, not a site-equivalence or representability premise.

The corepresentability argument follows the pinned Stacks proof in
`Sites.Continuous.PullbackOfSheafifiedYoneda`, with actual subcanonical
Yoneda sheaves instead of their sheafifications and no density import.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestLargeSiteYoneda
universe u

section General
variable {C D : Type (u+1)} [Category.{u} C] [Category.{u} D]
  (i : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.Subcanonical] [K.Subcanonical] [i.IsContinuous J K]
  [(i.sheafPushforwardContinuous (Type (u+1)) J K).IsRightAdjoint]

/-- The actual inverse-image corepresentability bijection. -/
def pullbackYonedaEquiv (U : C) (G : Sheaf K (Type (u+1))) :
    ((i.sheafPullback (Type (u+1)) J K).obj
      (J.uliftYoneda.{u+1}.obj U) ⟶ G) ≃ G.obj.obj (op (i.obj U)) :=
  ((i.sheafAdjunctionContinuous (Type (u+1)) J K).homEquiv _ _).trans
    (J.uliftYonedaEquiv.{u+1})

set_option backward.isDefEq.respectTransparency false in
omit [K.Subcanonical] in
/-- Corepresentability is natural in the actual target sheaf. -/
theorem pullbackYonedaEquiv_naturality (U : C)
    {G G' : Sheaf K (Type (u+1))} (α : G ⟶ G')
    (f : (i.sheafPullback (Type (u+1)) J K).obj
      (J.uliftYoneda.{u+1}.obj U) ⟶ G) :
    pullbackYonedaEquiv i J K U G' (f ≫ α) =
      α.hom.app (op (i.obj U)) (pullbackYonedaEquiv i J K U G f) := by
  simp only [pullbackYonedaEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right]
  exact J.uliftYonedaEquiv_comp _ _

/-- The two actual corepresented functors agree on every original sheaf. -/
def pullbackYonedaCorepIso (U : C) :
    coyoneda.obj (op ((i.sheafPullback (Type (u+1)) J K).obj
        (J.uliftYoneda.{u+1}.obj U))) ≅
      coyoneda.obj (op (K.uliftYoneda.{u+1}.obj (i.obj U))) :=
  NatIso.ofComponents (fun G => Equiv.toIso
    ((pullbackYonedaEquiv i J K U G).trans (K.uliftYonedaEquiv.{u+1}).symm)) (by
    intro G G' α
    ext f
    change (K.uliftYonedaEquiv.{u+1}).symm
        (pullbackYonedaEquiv i J K U G' (f ≫ α)) =
      (K.uliftYonedaEquiv.{u+1}).symm (pullbackYonedaEquiv i J K U G f) ≫ α
    apply (K.uliftYonedaEquiv.{u+1}).injective
    rw [Equiv.apply_symm_apply, pullbackYonedaEquiv_naturality,
      K.uliftYonedaEquiv_comp, Equiv.apply_symm_apply])

/-- The extension of an actual represented sheaf is the same original scheme. -/
def pullbackYonedaIso (U : C) :
    (i.sheafPullback (Type (u+1)) J K).obj
        (J.uliftYoneda.{u+1}.obj U) ≅
      K.uliftYoneda.{u+1}.obj (i.obj U) :=
  ((Coyoneda.fullyFaithful (C := Sheaf K (Type (u+1)))).preimageIso
    (pullbackYonedaCorepIso i J K U)).unop.symm

/-- The actual isomorphism respects the actual adjunction/Yoneda pairing. -/
theorem pullbackYonedaIso_hom_comp (U : C) (G : Sheaf K (Type (u+1)))
    (g : K.uliftYoneda.{u+1}.obj (i.obj U) ⟶ G) :
    pullbackYonedaEquiv i J K U G ((pullbackYonedaIso i J K U).hom ≫ g) =
      K.uliftYonedaEquiv.{u+1} g := by
  have key : (pullbackYonedaIso i J K U).hom ≫ g =
      (pullbackYonedaEquiv i J K U G).symm (K.uliftYonedaEquiv.{u+1} g) := by
    have hmap : coyoneda.map
        ((Coyoneda.fullyFaithful (C := Sheaf K (Type (u+1)))).preimageIso
          (pullbackYonedaCorepIso i J K U)).inv =
        (pullbackYonedaCorepIso i J K U).inv :=
      (Coyoneda.fullyFaithful (C := Sheaf K (Type (u+1)))).map_preimage _
    have hpre : (pullbackYonedaIso i J K U).hom ≫ g =
        (coyoneda.map ((Coyoneda.fullyFaithful (C := Sheaf K (Type (u+1)))).preimageIso
          (pullbackYonedaCorepIso i J K U)).inv).app G g := rfl
    rw [hpre, hmap]
    simp [pullbackYonedaCorepIso, NatIso.ofComponents_inv_app,
      Equiv.toIso_inv_hom_apply, Equiv.symm_symm]
  rw [key, Equiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
omit [K.Subcanonical] in
/-- Corepresentability is natural in the actual scheme map. -/
theorem pullbackYonedaEquiv_naturality_obj {U V : C} (g : U ⟶ V)
    (G : Sheaf K (Type (u+1)))
    (f : (i.sheafPullback (Type (u+1)) J K).obj
      (J.uliftYoneda.{u+1}.obj V) ⟶ G) :
    pullbackYonedaEquiv i J K U G
        ((i.sheafPullback (Type (u+1)) J K).map (J.uliftYoneda.{u+1}.map g) ≫ f) =
      G.obj.map (i.map g).op (pullbackYonedaEquiv i J K V G f) := by
  simp only [pullbackYonedaEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left]
  exact (J.uliftYonedaEquiv_naturality _ g).symm

set_option backward.isDefEq.respectTransparency false in
/-- Extension preserves represented schemes naturally, with literal scheme maps. -/
def pullbackCompYonedaIso :
    J.uliftYoneda.{u+1} ⋙ i.sheafPullback (Type (u+1)) J K ≅
      i ⋙ K.uliftYoneda.{u+1} :=
  NatIso.ofComponents (fun U => pullbackYonedaIso i J K U) (by
    intro U V g
    apply (pullbackYonedaEquiv i J K U _).injective
    dsimp only [Functor.comp_obj, Functor.comp_map]
    rw [pullbackYonedaEquiv_naturality_obj,
      pullbackYonedaIso_hom_comp]
    have h := pullbackYonedaIso_hom_comp i J K V _ (𝟙 _)
    simp only [Category.comp_id] at h
    rw [h]
    simpa using K.uliftYonedaEquiv_naturality
      (𝟙 (K.uliftYoneda.{u+1}.obj (i.obj V))) (i.map g))

end General

open AllTestBoundedCharts AllTestLargeSitePullback
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- The full-original-site extension preserves the same original schemes/maps. -/
def extendCompYonedaIso :
    (BigFppfOver.topology B (Spec (.of K)) hK).uliftYoneda.{u+1} ⋙
        extendSheaf K B hK ≅
      boundedInclusion B K hK ⋙
        (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)).uliftYoneda.{u+1} :=
  pullbackCompYonedaIso _ _ _

end M9StacksIntegration.AllTestLargeSiteYoneda
