module

public import M9StacksIntegration.AllTestBoundedCurveSmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# Actual properness and finite presentation of the restricted original family

The properness proof uses the original cartesian schematic cover and the
proved native fppf descent theorem. Finite presentation follows from the
actual smoothness, quasi-compactness and separatedness of this projection.
No properness, finite-presentation or classification premise is supplied.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestBoundedCurveProper
open AllTestBoundedCharts AllTestBoundedRestriction AllTestBoundedCartesian
  AllTestBoundedAlgebraicSpace AllTestBoundedCurveSmooth
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The native projection of every original all-test family is proper over
the original field and its entire bounded test base. -/
theorem restrictedFamilyMap_proper
    {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    Space.IsProper B (Spec (.of K)) hK (restrictedFamilyMap K B hK F).hom := by
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
  have hqn := Space.isProper_yoneda_map B (Spec (.of K)) hK qn hq.1
  exact property_of_schematic_cover K B hK
    (Space.properProperty B (Spec (.of K)) hK)
    (restrictedFamilySpace K B hK F) (chartMap K B hK Zn r)
    (baseMap K B hK T F.projection) qn vn
    (chart_isPullback K B hK qn vn r F.projection hcart) hs hv hqn

/-- Finite presentation is derived from the actual proper smooth projection. -/
theorem restrictedFamilyMap_finitePresentation
    {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    Space.IsFinitePresentation B (Spec (.of K)) hK (restrictedFamilyMap K B hK F).hom :=
  ⟨Space.isLocallyOfFinitePresentation_of_isSmooth B (Spec (.of K)) hK
      (restrictedFamilyMap_smooth_one K B hK F).1,
    (restrictedFamilyMap_proper K B hK F).2.1.2,
    Space.isQuasiSeparated_of_isSeparated B (Spec (.of K)) hK
      (restrictedFamilyMap_proper K B hK F).1⟩

end M9StacksIntegration.AllTestBoundedCurveProper
