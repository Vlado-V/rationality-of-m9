module

public import M9StacksIntegration.AllTestNativeCurveFamily
public import M9StacksIntegration.NativeSchematicCurveFamily
public import M9StacksIntegration.AllTestNativeFieldSchemeModel

/-!
# SAME-base comparison of the two actual schematic family constructions

Restricting the literal original represented scheme family and applying the
actual lower-shriek functor gives the SAME actual native schematic family.
The total-space isomorphism is actual restriction-Yoneda followed by actual
relocalization-Yoneda. Their actual naturalities prove projection compatibility;
the family isomorphism has IDENTITY base map. This holds for arbitrary bounded
bases, using relative dimension one rather than total dimension ≤1.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestNativeSchemeFamilyComparison
open AllTestBoundedCharts AllTestBoundedRestriction AllTestBoundedCartesian
  AllTestNativeCurveFamily AllTestNativeCartesianCover AllTestSchemeFamilies
universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual total-space comparison retains the SAME represented scheme. -/
def schemeFamilyTotalIso
    {Z T : BigFppfOver B (Spec (.of K)) hK} (q : Z ⟶ T) (g : ℕ)
    (hq : M9StandaloneDraft.SchemeCurve ((BigFppfOver.toScheme B (Spec (.of K)) hK).map q) g) :
    nativeTotal B hZ K hK
        (standaloneSchemeFamily K ((boundedInclusion B K hK).map q) g hq) ≅
      schemeSpace ((Over.map (fieldToInteger B hZ K hK)).obj Z) :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    (((OverShriek.relocalizePresheafFunctor (fieldToInteger B hZ K hK)).mapIso
      (restrictRepresentableIso B K hK Z)) ≪≫
      relocalizedYonedaIso B (B.obj hK) (B.obj hZ) (fieldToInteger B hZ K hK) Z)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The genuine native image of the literal original scheme family is the
SAME native schematic family, over the IDENTITY original base. -/
def nativeSchemeFamilyIso
    {Z T : BigFppfOver B (Spec (.of K)) hK} (q : Z ⟶ T) (g : ℕ)
    (hq : M9StandaloneDraft.SchemeCurve ((BigFppfOver.toScheme B (Spec (.of K)) hK).map q) g) :
    nativeCurveFamily B hZ K hK
        (standaloneSchemeFamily K ((boundedInclusion B K hK).map q) g hq) ≅
      NativeSchematicCurveFamily.schemeCurveFamily B hZ
        ((Over.map (fieldToInteger B hZ K hK)).map q) g hq := by
  let k := fieldToInteger B hZ K hK
  let L := OverShriek.relocalizePresheafFunctor k
  let F := standaloneSchemeFamily K ((boundedInclusion B K hK).map q) g hq
  let eZ := restrictRepresentableIso B K hK Z
  let eT := restrictRepresentableIso B K hK T
  let rZ := relocalizedYonedaIso B (B.obj hK) (B.obj hZ) k Z
  let rT := relocalizedYonedaIso B (B.obj hK) (B.obj hZ) k T
  apply AllTestNativeFieldSchemeModel.isoMk
    (F := nativeCurveFamily B hZ K hK F)
    (G := NativeSchematicCurveFamily.schemeCurveFamily B hZ ((Over.map k).map q) g hq)
    (Iso.refl ((Over.map k).obj T)) (schemeFamilyTotalIso B hZ K hK q g hq)
  apply ObjectProperty.hom_ext
  change (L.map eZ.hom ≫ rZ.hom) ≫ yoneda.map ((Over.map k).map q) =
    (L.map (baseMap K B hK T F.projection) ≫ rT.hom) ≫ yoneda.map (𝟙 ((Over.map k).obj T))
  rw [(yoneda (C := BigFppfOver B integerBase hZ)).map_id, Category.comp_id]
  calc
    (L.map eZ.hom ≫ rZ.hom) ≫ yoneda.map ((Over.map k).map q) =
        L.map eZ.hom ≫ (rZ.hom ≫ yoneda.map ((Over.map k).map q)) := Category.assoc _ _ _
    _ = L.map eZ.hom ≫ (L.map (yoneda.map q) ≫ rT.hom) :=
      congrArg (fun m => L.map eZ.hom ≫ m)
        (relocalizedYonedaIso_naturality B (B.obj hK) (B.obj hZ) k q).symm
    _ = L.map (eZ.hom ≫ yoneda.map q) ≫ rT.hom := by rw [L.map_comp, Category.assoc]
    _ = L.map (restrictMap K B hK (yoneda.map ((boundedInclusion B K hK).map q)) ≫ eT.hom) ≫ rT.hom :=
      congrArg (fun m => L.map m ≫ rT.hom) (restrictRepresentableIso_naturality K B hK q).symm
    _ = L.map (baseMap K B hK T F.projection) ≫ rT.hom := rfl

/-- Literal IDENTITY base map, excluding any field or base automorphism. -/
theorem nativeSchemeFamilyIso_baseMap
    {Z T : BigFppfOver B (Spec (.of K)) hK} (q : Z ⟶ T) (g : ℕ)
    (hq : M9StandaloneDraft.SchemeCurve ((BigFppfOver.toScheme B (Spec (.of K)) hK).map q) g) :
    (nativeSchemeFamilyIso B hZ K hK q g hq).hom.baseMap =
      𝟙 ((Over.map (fieldToInteger B hZ K hK)).obj T) := rfl

end M9StacksIntegration.AllTestNativeSchemeFamilyComparison
