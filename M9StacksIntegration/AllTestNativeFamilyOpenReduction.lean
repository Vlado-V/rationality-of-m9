module

public import M9StacksIntegration.AllTestNativeOpenLocusDescent
public import M9StacksIntegration.AllTestNativeCurveNaturality
public import M9StacksIntegration.AllTestSingleSchematicCover

/-!
# Actual schematic reduction for ORIGINAL nonschematic families

Every literal original family has a genuinely constructed bounded schematic
etale-surjective Cartesian cover. Its actual native image supplies an actual
native curve-family arrow over the SAME surjective scheme map. Consequently
any genuinely proved open curve-family property reduces to its SAME-base
schematic case. This is a general local reduction, not a claim that native
M_g openness or the final all-test moduli comparison has already been proved.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestNativeFamilyOpenReduction
open AllTestBoundedCharts AllTestNativeCurveFamily AllTestNativeCurveNaturality
  AllTestNativeOpenLocusDescent AllTestSingleSchematicCover AllTestSchemeFamilies
universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

set_option backward.defeqAttrib.useBackward true in
/-- ACTUAL schematic covers reduce a genuine open family property to its
schematic case, for EVERY original family including nonschematic totals.
The open-locus and schematic-property hypotheses are explicit mathematical
inputs to this generic reduction; no classifier/equivalence is supplied. -/
theorem nativeFamily_property_of_schematic
    {P : ObjectProperty (CurveFamily B hZ)} (hP : IsOpenCurvesLocus B hZ P)
    (g : ℕ)
    (hsch : ∀ {Z U : BigFppfOver B (Spec (.of K)) hK} (q : Z ⟶ U)
      (hq : M9StandaloneDraft.SchemeCurve ((BigFppfOver.toScheme B (Spec (.of K)) hK).map q) g),
      P (nativeCurveFamily B hZ K hK
        (standaloneSchemeFamily K ((boundedInclusion B K hK).map q) g hq)))
    {T : BigFppfOver B (Spec (.of K)) hK}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    P (nativeCurveFamily B hZ K hK F) := by
  have hT : B.Contains ((boundedInclusion B K hK).obj T).left := T.left.property
  obtain ⟨U, Z, v, q, r, hU, hZs, hv, hs, hcart, hq⟩ :=
    exists_bounded_schematic_etale_cover B K
      (T := (boundedInclusion B K hK).obj T) (g := g) hT F
  rcases U with ⟨U, ⟨⟨⟩⟩, Uhom⟩
  rcases Z with ⟨Z, ⟨⟨⟩⟩, Zhom⟩
  let Un := siteObject B (Spec (.of K)) hK hU Uhom
  let Zn := siteObject B (Spec (.of K)) hK hZs Zhom
  let qn : Zn ⟶ Un := boundedPreimage B K hK q
  let vn : Un ⟶ T := boundedPreimage B K hK v
  let G : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj Un) g :=
    standaloneSchemeFamily K ((boundedInclusion B K hK).map qn) g hq
  have hcartG : IsPullback r G.projection F.projection
      (yoneda.map ((boundedInclusion B K hK).map vn)) := hcart
  have hG : P (nativeCurveFamily B hZ K hK G) := hsch (Z := Zn) (U := Un) qn hq
  let δ : nativeCurveFamily B hZ K hK G ⟶ nativeCurveFamily B hZ K hK F :=
    nativeCartesianMap B hZ K hK vn F G r hcartG
  have hδ : Surjective ((BigFppfOver.toScheme B integerBase hZ).map δ.baseMap) := hs
  exact property_of_hom_surjective B hZ hP δ hδ hG

end M9StacksIntegration.AllTestNativeFamilyOpenReduction
