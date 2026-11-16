module

public import M9StacksIntegration.AllTestBoundedAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothOfRelativeDimensionRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat

/-!
# Actual relative smoothness of the original family's native projection

The same original cartesian schematic cover proves smoothness of relative
dimension one of the restricted native projection, by the proved fppf
locality theorem. The projection is a map of the actual native algebraic
spaces already constructed from the unchanged all-test family.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestBoundedCurveSmooth
open AllTestBoundedCharts AllTestBoundedRestriction AllTestBoundedCartesian
  AllTestBoundedAlgebraicSpace
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A property local on the actual native fppf target descends from one
actual cartesian schematic etale-surjective chart. -/
theorem property_of_schematic_cover
    (P : MorphismProperty (AlgebraicSpaces B (Spec (.of K)) hK))
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u+1} B (Spec (.of K)) hK)]
    (X : AlgebraicSpaces B (Spec (.of K)) hK)
    {Z U T : BigFppfOver B (Spec (.of K)) hK}
    (r : yoneda.obj Z ⟶ X.obj) (π : X.obj ⟶ yoneda.obj T)
    (q : Z ⟶ U) (v : U ⟶ T)
    (h : IsPullback r (yoneda.map q) π (yoneda.map v))
    (hs : Surjective ((BigFppfOver.toScheme B (Spec (.of K)) hK).map v))
    (he : Etale ((BigFppfOver.toScheme B (Spec (.of K)) hK).map v))
    (hq : P (schemeSpaceMap q)) :
    P (ObjectProperty.homMk π : X ⟶ schemeSpace T) := by
  let f : X ⟶ schemeSpace T := ObjectProperty.homMk π
  let a : schemeSpace U ⟶ schemeSpace T := schemeSpaceMap v
  have hsq : IsPullback (ObjectProperty.homMk r : schemeSpace Z ⟶ X)
      (schemeSpaceMap q) f a :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι (IsAlgebraicSpace B (Spec (.of K)) hK)) h
  have hR := Space.ofArrows_atlas_mem_fppf_precoverage.{u, u+1} B (Spec (.of K)) hK
    (isAlgebraicSpace_yoneda B (Spec (.of K)) hK T)
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B (Spec (.of K)) hK _ v).2 hs)
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B (Spec (.of K)) hK _ v).2 he)
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd hR
  intro V g _ hg
  obtain ⟨i⟩ := hg
  change P (pullback.snd f a)
  rw [← hsq.isoPullback_inv_snd]
  exact (P.cancel_left_of_respectsIso _ _).mpr hq

/-- The actual native morphism retains the original restricted projection. -/
def restrictedFamilyMap
    {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    restrictedFamilySpace K B hK F ⟶ schemeSpace T :=
  ObjectProperty.homMk (baseMap K B hK T F.projection)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- EVERY original all-test family has a native restricted projection smooth
of relative dimension one, over the original field and entire bounded base. -/
theorem restrictedFamilyMap_smooth_one
    {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    Space.IsSmoothOfRelativeDimension B (Spec (.of K)) hK 1
      (restrictedFamilyMap K B hK F).hom := by
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
  let : SmoothOfRelativeDimension 1
      ((BigFppfOver.toScheme B (Spec (.of K)) hK).map qn) := hq.2.1
  have hqn := Space.isSmoothOfRelativeDimension_yoneda_map B (Spec (.of K)) hK qn 1
  exact property_of_schematic_cover K B hK
    (Space.smoothOfRelativeDimensionProperty B (Spec (.of K)) hK 1)
    (restrictedFamilySpace K B hK F) (chartMap K B hK Zn r)
    (baseMap K B hK T F.projection) qn vn
    (chart_isPullback K B hK qn vn r F.projection hcart) hs hv hqn

/-- Flatness is derived from the actual smooth restricted projection. -/
theorem restrictedFamilyMap_flat
    {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    Space.IsFlat B (Spec (.of K)) hK (restrictedFamilyMap K B hK F).hom :=
  Space.isFlat_of_isSmooth B (Spec (.of K)) hK _ (restrictedFamilyMap_smooth_one K B hK F).1

end M9StacksIntegration.AllTestBoundedCurveSmooth
