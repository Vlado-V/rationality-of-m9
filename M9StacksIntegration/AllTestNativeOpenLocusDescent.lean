module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstack
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering

/-!
# Actual descent of open curve-family properties

A genuine open locus of curve families descends along an actual surjective
base map: the actual factorization of the covering family makes the open
contain every point of the original base. The native open-subspace
factorization theorem then constructs the identity-base factorization.
This lemma does not assume or construct a moduli classifier; its open-locus
argument must itself come from a genuinely proved native property theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestNativeOpenLocusDescent
universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- Genuine open-locus properties descend along ACTUAL surjective base maps.
Neither local membership nor an open-locus assertion is silently substituted
for the desired global property: actual point surjectivity proves it. -/
theorem property_of_hom_surjective
    {P : ObjectProperty (CurveFamily B hZ)} (hP : IsOpenCurvesLocus B hZ P)
    {F G : CurveFamily B hZ} (δ : F ⟶ G)
    (hδ : Surjective ((BigFppfOver.toScheme B integerBase hZ).map δ.baseMap))
    (hF : P F) : P G := by
  obtain ⟨W, hW, hchar⟩ := hP G
  have hsurj : (MorphismProperty.inverseImage (@Surjective.{u})
      (BigFppfOver.toScheme B integerBase hZ)).presheaf (yoneda.map δ.baseMap) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B integerBase hZ
      (@Surjective.{u}) δ.baseMap).mpr hδ
  have hpoints : Function.Surjective
      (Space.pointsMap B integerBase hZ (schemeSpace F.base).obj
        (schemeSpaceMap δ.baseMap).hom) :=
    (Space.surjective_iff_surjective_pointsMap B integerBase hZ
      (schemeSpace G.base).obj (schemeSpace G.base).property F.base
      (schemeSpaceMap δ.baseMap).hom).mp hsurj
  have himage := (Space.factorsThrough_openSubspace_iff_points B integerBase hZ
    (schemeSpace G.base).property (schemeSpace F.base).property W hW
    (schemeSpaceMap δ.baseMap).hom).mp ((hchar F δ).mp hF)
  have hid : ∃ t : (schemeSpace G.base).obj ⟶ W.toFunctor, t ≫ W.ι = 𝟙 _ := by
    apply (Space.factorsThrough_openSubspace_iff_points B integerBase hZ
      (schemeSpace G.base).property (schemeSpace G.base).property W hW (𝟙 _)).mpr
    intro x _
    obtain ⟨y, hy⟩ := hpoints x
    exact himage ⟨y, hy⟩
  apply (hchar G (𝟙 G)).mpr
  change ∃ t : (schemeSpace G.base).obj ⟶ W.toFunctor,
    t ≫ W.ι = yoneda.map (𝟙 G.base)
  rw [(yoneda (C := BigFppfOver B integerBase hZ)).map_id]
  exact hid

end M9StacksIntegration.AllTestNativeOpenLocusDescent
