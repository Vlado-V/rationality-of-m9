module

public import M9StacksIntegration.AllTestNativeCoefficientCharts
public import M9StacksIntegration.AllTestNativeCoefficientSchemes
public import M9StacksIntegration.AllTestNativeRepresentedCurveGeometry
public import M9StacksIntegration.AllTestNativeOriginalPullbacks
public import M9StacksIntegration.AllTestNativeOriginalNormalizedSchemes

/-!
# Genuine original schematic charts of the inverse coefficient space

The actual inverse coefficient-space projection is read on ALL original
schemes. Its actual native Cartesian charts become literal original
Cartesian squares with precisely the same original scheme maps.
No supplied original Cartesian comparison or classifier is used.
The same-scheme comparisons are normalized by the ACTUAL recovery unit,
so the projection retains the exact original base/coefficient map.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestNativeOriginalCurveCharts
open AllTestNativeCoefficientProjection AllTestNativeCoefficientSpace
  AllTestNativeCoefficientCharts AllTestNativeOriginalSpace
  AllTestNativeOriginalFunctor AllTestNativeOriginalSchemes
  AllTestNativeOriginalPullbacks AllTestBoundedCharts AllTestNativeOriginalNormalizedSchemes
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hZ : B.Contains integerBase) (hK : B.Contains (Spec (.of K)))

local notation "k" => AllTestNativeCurveFamily.fieldToInteger B hZ K hK

/-- The actual coefficient inverse total on ALL original test schemes. -/
abbrev originalTotal
    {X : AlgebraicSpaces B integerBase hZ}
    (T : BigFppfOver B (Spec (.of K)) hK)
    (π : X.obj ⟶ yoneda.obj ((Over.map k).obj T)) : M9StandaloneDraft.Space K :=
  let H := projectionSpace B (Spec (.of K)) integerBase hK hZ k T π
  originalSpaceOfNative K B hK H.obj H.property

/-- The actual original projection to the SAME represented base scheme. -/
def originalProjection
    {X : AlgebraicSpaces B integerBase hZ}
    (T : BigFppfOver B (Spec (.of K)) hK)
    (π : X.obj ⟶ yoneda.obj ((Over.map k).obj T)) :
    (originalTotal K B hZ hK T π).obj ⟶ yoneda.obj ((boundedInclusion B K hK).obj T) :=
  (originalPresheafFunctor K B hK).map
      (nativeProjection B (Spec (.of K)) integerBase hK hZ k T π) ≫
    (normalizedSchemeIso K B hK T).hom

/-- The actual coefficient-preserving chart on the FULL original test site. -/
def originalCurveChart
    {X : AlgebraicSpaces B integerBase hZ}
    {Z U T : BigFppfOver B (Spec (.of K)) hK}
    (π : X.obj ⟶ yoneda.obj ((Over.map k).obj T))
    (q : Z ⟶ U) (v : U ⟶ T)
    (p : yoneda.obj ((Over.map k).obj Z) ⟶ X.obj)
    (hcart : IsPullback p (yoneda.map ((Over.map k).map q))
      π (yoneda.map ((Over.map k).map v))) :
    yoneda.obj ((boundedInclusion B K hK).obj Z) ⟶
      (originalTotal K B hZ hK T π).obj :=
  (normalizedSchemeIso K B hK Z).inv ≫
    (originalPresheafFunctor K B hK).map (ObjectProperty.homMk
      (chartMap B (Spec (.of K)) integerBase hK hZ k π q v p hcart))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The original chart square is ACTUALLY Cartesian on every original test;
no original square or factorization is a premise. -/
theorem originalCurveChart_isPullback
    {X : AlgebraicSpaces B integerBase hZ}
    {Z U T : BigFppfOver B (Spec (.of K)) hK}
    (π : X.obj ⟶ yoneda.obj ((Over.map k).obj T))
    (q : Z ⟶ U) (v : U ⟶ T)
    (p : yoneda.obj ((Over.map k).obj Z) ⟶ X.obj)
    (hcart : IsPullback p (yoneda.map ((Over.map k).map q))
      π (yoneda.map ((Over.map k).map v))) :
    IsPullback (originalCurveChart K B hZ hK π q v p hcart)
      (yoneda.map ((boundedInclusion B K hK).map q))
      (originalProjection K B hZ hK T π)
      (yoneda.map ((boundedInclusion B K hK).map v)) := by
  let H := projectionSpace B (Spec (.of K)) integerBase hK hZ k T π
  let r := chartMap B (Spec (.of K)) integerBase hK hZ k π q v p hcart
  let f := nativeProjection B (Spec (.of K)) integerBase hK hZ k T π
  have hi := original_isPullback K B hK
    (ObjectProperty.homMk r : schemeSpace Z ⟶ H)
    (schemeSpaceMap q) f (schemeSpaceMap v)
    (chartMap_isPullback B (Spec (.of K)) integerBase hK hZ k π q v p hcart)
  apply hi.of_iso (normalizedSchemeIso K B hK Z) (Iso.refl _)
    (normalizedSchemeIso K B hK U) (normalizedSchemeIso K B hK T)
  · simp only [Iso.refl_hom, Category.comp_id, originalCurveChart,
      Iso.hom_inv_id_assoc]
    rfl
  · exact normalizedSchemeIso_naturality K B hK q
  · rfl
  · exact normalizedSchemeIso_naturality K B hK v

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Literal native recovery of the SAME original projection, over the
IDENTITY base and the ORIGINAL coefficient map. -/
theorem originalProjection_restrict
    {X : AlgebraicSpaces B integerBase hZ}
    (T : BigFppfOver B (Spec (.of K)) hK)
    (π : X.obj ⟶ yoneda.obj ((Over.map k).obj T)) :
    AllTestBoundedCartesian.baseMap K B hK T (originalProjection K B hZ hK T π) =
      (AllTestBoundedOriginalRecovery.originalNativeRestrictionSmallIso K B hK
        (projectionSpace B (Spec (.of K)) integerBase hK hZ k T π).obj
        (projectionSpace B (Spec (.of K)) integerBase hK hZ k T π).property).hom ≫
      (nativeProjection B (Spec (.of K)) integerBase hK hZ k T π).hom := by
  let f := nativeProjection B (Spec (.of K)) integerBase hK hZ k T π
  let R := AllTestBoundedAlgebraicSpace.restrictionFunctor K B hK
  change R.map ((originalPresheafFunctor K B hK).map f ≫
      (normalizedSchemeIso K B hK T).hom) ≫ (restrictRepresentableIso B K hK T).hom = _
  rw [R.map_comp]
  change (AllTestBoundedRestriction.restrictMap K B hK
        ((originalPresheafFunctor K B hK).map f) ≫
      AllTestBoundedRestriction.restrictMap K B hK (normalizedSchemeIso K B hK T).hom) ≫
      (restrictRepresentableIso B K hK T).hom = _
  rw [Category.assoc, normalizedSchemeIso_restrict]
  exact AllTestNativeOriginalUnit.originalNativeRestrictionSmallIso_naturality K B hK f

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Literal native recovery of the SAME original schematic chart. -/
theorem originalCurveChart_restrict
    {X : AlgebraicSpaces B integerBase hZ}
    {Z U T : BigFppfOver B (Spec (.of K)) hK}
    (π : X.obj ⟶ yoneda.obj ((Over.map k).obj T))
    (q : Z ⟶ U) (v : U ⟶ T)
    (p : yoneda.obj ((Over.map k).obj Z) ⟶ X.obj)
    (hcart : IsPullback p (yoneda.map ((Over.map k).map q))
      π (yoneda.map ((Over.map k).map v))) :
    AllTestBoundedCartesian.chartMap K B hK Z
        (originalCurveChart K B hZ hK π q v p hcart) ≫
      (AllTestBoundedOriginalRecovery.originalNativeRestrictionSmallIso K B hK
        (projectionSpace B (Spec (.of K)) integerBase hK hZ k T π).obj
        (projectionSpace B (Spec (.of K)) integerBase hK hZ k T π).property).hom =
      chartMap B (Spec (.of K)) integerBase hK hZ k π q v p hcart := by
  let R := AllTestBoundedAlgebraicSpace.restrictionFunctor K B hK
  let e := normalizedSchemeIso K B hK Z
  let eZ := AllTestBoundedOriginalRecovery.originalNativeRestrictionSmallIso K B hK
    (schemeSpace Z).obj (schemeSpace Z).property
  let H := projectionSpace B (Spec (.of K)) integerBase hK hZ k T π
  let eH := AllTestBoundedOriginalRecovery.originalNativeRestrictionSmallIso K B hK H.obj H.property
  let r := chartMap B (Spec (.of K)) integerBase hK hZ k π q v p hcart
  have hnorm : R.map e.hom ≫ (restrictRepresentableIso B K hK Z).hom = eZ.hom :=
    normalizedSchemeIso_restrict K B hK Z
  have hZunit : R.map e.inv ≫ eZ.hom = (restrictRepresentableIso B K hK Z).hom := by
    calc
      _ = R.map e.inv ≫ (R.map e.hom ≫ (restrictRepresentableIso B K hK Z).hom) :=
        congrArg (fun m => R.map e.inv ≫ m) hnorm.symm
      _ = (R.map e.inv ≫ R.map e.hom) ≫ (restrictRepresentableIso B K hK Z).hom :=
        (Category.assoc _ _ _).symm
      _ = R.map (e.inv ≫ e.hom) ≫ (restrictRepresentableIso B K hK Z).hom :=
        congrArg (fun m => m ≫ (restrictRepresentableIso B K hK Z).hom) (R.map_comp _ _).symm
      _ = _ := by rw [e.inv_hom_id, R.map_id, Category.id_comp]
  have hr : R.map ((originalPresheafFunctor K B hK).map
      (ObjectProperty.homMk r : schemeSpace Z ⟶ H)) ≫ eH.hom = eZ.hom ≫ r :=
    AllTestNativeOriginalUnit.originalNativeRestrictionSmallIso_naturality K B hK
      (ObjectProperty.homMk r : schemeSpace Z ⟶ H)
  change ((restrictRepresentableIso B K hK Z).inv ≫
      R.map (e.inv ≫ (originalPresheafFunctor K B hK).map
        (ObjectProperty.homMk r : schemeSpace Z ⟶ H))) ≫ eH.hom = r
  rw [R.map_comp]
  calc
    _ = (restrictRepresentableIso B K hK Z).inv ≫ R.map e.inv ≫
        (R.map ((originalPresheafFunctor K B hK).map
          (ObjectProperty.homMk r : schemeSpace Z ⟶ H)) ≫ eH.hom) := by
      simp only [Category.assoc]
    _ = (restrictRepresentableIso B K hK Z).inv ≫ R.map e.inv ≫ (eZ.hom ≫ r) :=
      congrArg (fun m => (restrictRepresentableIso B K hK Z).inv ≫ R.map e.inv ≫ m) hr
    _ = (restrictRepresentableIso B K hK Z).inv ≫ (R.map e.inv ≫ eZ.hom) ≫ r := by
      simp only [Category.assoc]
    _ = (restrictRepresentableIso B K hK Z).inv ≫ (restrictRepresentableIso B K hK Z).hom ≫ r := by
      rw [hZunit]
    _ = r := Iso.inv_hom_id_assoc _ _

/-- Actual recovery of the ORIGINAL native total from the inverse
coefficient space, with no total-space comparison premise. -/
def originalTotalRelocalizeIso
    {X : AlgebraicSpaces B integerBase hZ}
    (T : BigFppfOver B (Spec (.of K)) hK)
    (π : X.obj ⟶ yoneda.obj ((Over.map k).obj T)) :
    (OverShriek.relocalizePresheafFunctor k).obj
        (AllTestBoundedRestriction.restrict K B hK (originalTotal K B hZ hK T π).obj) ≅ X.obj :=
  (OverShriek.relocalizePresheafFunctor k).mapIso
    (AllTestBoundedOriginalRecovery.originalNativeRestrictionSmallIso K B hK
      (projectionSpace B (Spec (.of K)) integerBase hK hZ k T π).obj
      (projectionSpace B (Spec (.of K)) integerBase hK hZ k T π).property) ≪≫
    coefficientRelocalizeIso B (Spec (.of K)) integerBase hK hZ k X
      (projectionCoefficient B (Spec (.of K)) integerBase hK hZ k T π)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The native recovery retains the ORIGINAL projection to the SAME base,
not merely the total space or a base-automorphism orbit. -/
theorem originalProjection_relocalize
    {X : AlgebraicSpaces B integerBase hZ}
    (T : BigFppfOver B (Spec (.of K)) hK)
    (π : X.obj ⟶ yoneda.obj ((Over.map k).obj T)) :
    (originalTotalRelocalizeIso K B hZ hK T π).hom ≫ π =
      (OverShriek.relocalizePresheafFunctor k).map
        (AllTestBoundedCartesian.baseMap K B hK T (originalProjection K B hZ hK T π)) ≫
      (relocalizedYonedaIso B (B.obj hK) (B.obj hZ) k T).hom := by
  let L := OverShriek.relocalizePresheafFunctor k
  let H := projectionSpace B (Spec (.of K)) integerBase hK hZ k T π
  let e := AllTestBoundedOriginalRecovery.originalNativeRestrictionSmallIso K B hK H.obj H.property
  let f := nativeProjection B (Spec (.of K)) integerBase hK hZ k T π
  let c := coefficientRelocalizeIso B (Spec (.of K)) integerBase hK hZ k X
    (projectionCoefficient B (Spec (.of K)) integerBase hK hZ k T π)
  let eT := relocalizedYonedaIso B (B.obj hK) (B.obj hZ) k T
  change (L.map e.hom ≫ c.hom) ≫ π =
    L.map (AllTestBoundedCartesian.baseMap K B hK T
      (originalProjection K B hZ hK T π)) ≫ eT.hom
  calc
    _ = L.map e.hom ≫ (c.hom ≫ π) := Category.assoc _ _ _
    _ = L.map e.hom ≫ (L.map f.hom ≫ eT.hom) :=
      congrArg (fun m => L.map e.hom ≫ m)
        (nativeProjection_relocalize B (Spec (.of K)) integerBase hK hZ k T π).symm
    _ = L.map (e.hom ≫ f.hom) ≫ eT.hom := by rw [L.map_comp, Category.assoc]
    _ = _ := congrArg (fun m => L.map m ≫ eT.hom)
      (originalProjection_restrict K B hZ hK T π).symm

end M9StacksIntegration.AllTestNativeOriginalCurveCharts
