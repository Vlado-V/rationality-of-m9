module

public import M9StacksIntegration.AllTestBoundedCartesian
public import M9StacksIntegration.AllTestSingleSchematicCover

/-!
# A genuine bounded etale atlas of every original family

The single original cartesian schematic cover gives a represented atlas of
the restricted total presheaf. Its surjectivity and etaleness are proved
under every represented base change on the bounded site. This is an actual
atlas construction, not an assumed classifier or equivalence of families.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestBoundedAtlas
open AllTestBoundedCharts AllTestBoundedRestriction AllTestBoundedCartesian
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- Any stable scheme property of the original base cover holds on every
represented pullback of its actual restricted chart. -/
theorem chart_presheafProperty
    (P : MorphismProperty Scheme.{u}) [MorphismProperty.IsStableUnderBaseChange P]
    {F : M9StandaloneDraft.Presheaves K}
    {Z U T : BigFppfOver B (Spec (.of K)) hK} (q : Z ⟶ U) (v : U ⟶ T)
    (r : yoneda.obj ((boundedInclusion B K hK).obj Z) ⟶ F)
    (π : F ⟶ yoneda.obj ((boundedInclusion B K hK).obj T))
    (h : IsPullback r (yoneda.map ((boundedInclusion B K hK).map q)) π
      (yoneda.map ((boundedInclusion B K hK).map v)))
    (hv : P ((BigFppfOver.toScheme B (Spec (.of K)) hK).map v)) :
    (MorphismProperty.inverseImage P (BigFppfOver.toScheme B (Spec (.of K)) hK)).presheaf
      (chartMap K B hK Z r) := by
  let Q := MorphismProperty.inverseImage P (BigFppfOver.toScheme B (Spec (.of K)) hK)
  let : MorphismProperty.IsStableUnderBaseChange Q :=
    ⟨fun h hp => MorphismProperty.of_isPullback (P := P)
      (h.map (BigFppfOver.toScheme B (Spec (.of K)) hK)) hp⟩
  let : MorphismProperty.IsStableUnderBaseChange Q.presheaf :=
    MorphismProperty.relative_isStableUnderBaseChange Q
  have hv' : Q.presheaf (yoneda.map v) :=
    MorphismProperty.relative_map (P := Q) (F := yoneda) hv
  exact MorphismProperty.of_isPullback (chart_isPullback K B hK q v r π h).flip hv'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The restriction of EVERY original family over a bounded test base has
an actual representable surjective etale atlas. No size premise on its
original total space, diagonal-representation hypothesis, or classifier is
supplied: the original single schematic cover constructs this atlas. -/
theorem exists_restricted_etale_atlas
    {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    ∃ (Z : BigFppfOver B (Spec (.of K)) hK)
      (r : yoneda.obj Z ⟶ restrict K B hK F.total.obj),
      (MorphismProperty.inverseImage (@Surjective.{u})
        (BigFppfOver.toScheme B (Spec (.of K)) hK)).presheaf r ∧
      (MorphismProperty.inverseImage (@Etale.{u})
        (BigFppfOver.toScheme B (Spec (.of K)) hK)).presheaf r := by
  have hT : B.Contains ((boundedInclusion B K hK).obj T).left := T.left.property
  obtain ⟨U, Z, v, q, r, hU, hZ, hv, hs, hcart, hq⟩ :=
    AllTestSingleSchematicCover.exists_bounded_schematic_etale_cover B K
      (T := (boundedInclusion B K hK).obj T) (g := g) hT F
  rcases U with ⟨U, ⟨⟨⟩⟩, Uhom⟩
  rcases Z with ⟨Z, ⟨⟨⟩⟩, Zhom⟩
  let Un := siteObject B (Spec (.of K)) hK hU Uhom
  let Zn := siteObject B (Spec (.of K)) hK hZ Zhom
  let qn : Zn ⟶ Un := boundedPreimage B K hK q
  let vn : Un ⟶ T := boundedPreimage B K hK v
  refine ⟨Zn, chartMap K B hK Zn r, ?_, ?_⟩
  · exact chart_presheafProperty K B hK (@Surjective.{u}) qn vn r F.projection hcart hs
  · exact chart_presheafProperty K B hK (@Etale.{u}) qn vn r F.projection hcart hv

end M9StacksIntegration.AllTestBoundedAtlas
