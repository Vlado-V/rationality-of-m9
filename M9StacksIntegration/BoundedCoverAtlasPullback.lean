module

public import M9StacksIntegration.BoundedCoverFamily
public import M9StacksIntegration.NativeCoverFamilyAtlasArrow

/-! Genuine atlas pullbacks of actual bounded-cover families. The raw
original source pullback retains its cover map and degree data; the real
Cartesian family arrow and point lifting come from native representation. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.BoundedCoverAtlasPullback

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (D : BoundedCoverFamily B K)

abbrev sourceBase : BigFppfOver B (Spec (.of K)) hK :=
  siteObject B (Spec (.of K)) hK D.parameterContained D.structureMap
abbrev sourceTotal : BigFppfOver B integerBase hZ := integerSiteObject B hZ D.totalContained

/-- The original family map over its actual ground-field base. -/
def sourceProjection : sourceTotal B hZ K D ⟶
    (NativeCoverFamilyAtlasArrow.integerBaseFunctor B hZ K hK).obj (sourceBase B K hK D) :=
  Over.homMk (ObjectProperty.homMk D.projection) (by
    apply B.inclusion.map_injective
    exact specULiftZIsTerminal.hom_ext _ _)

/-- The full all-original-field curve condition is retained literally. -/
theorem source_schemeCurve : M9StandaloneDraft.SchemeCurve
    ((BigFppfOver.toScheme B integerBase hZ).map (sourceProjection B hZ K hK D)) 9 :=
  D.schemeCurve

instance sourceBase_quasiCompact : QuasiCompact (B.inclusion.map (sourceBase B K hK D).hom) := by
  change QuasiCompact D.structureMap
  infer_instance
instance sourceBase_finiteType : LocallyOfFiniteType (B.inclusion.map (sourceBase B K hK D).hom) :=
  D.finiteType

variable {V : BigFppfOver B (Spec (.of K)) hK}
  (b : Stack.schemeStack.{u,u+1} B (Spec (.of K)) hK V ⟶
    CoverFamilyStackPullback.sourceStack B hZ K hK)

abbrev classifier := NativeCoverFamilyAtlasArrow.sourceClassifier B hZ K hK
  (sourceBase B K hK D) (sourceProjection B hZ K hK D) (source_schemeCurve B hZ K hK D)

/-- Actual finite scheme representation and its actual universal native
comparison. These data are conclusions of `exists_data`. -/
structure Data where
  parameter : BigFppfOver B (Spec (.of K)) hK
  equivalence : StacksRepresentableCFG.EquivalenceOver (Over.forget parameter)
    (CoverFamilyStackPullback.pairProjection B hZ K hK (sourceBase B K hK D) V
      (classifier B hZ K hK D) b)
  point : CoverFamilyStackPullback.PointData B hZ K hK (sourceBase B K hK D) V
    (classifier B hZ K hK D) b (P := parameter)
  universal : equivalence.hom.functor.obj (Over.mk (𝟙 parameter)) =
    CoverFamilyStackPullback.pointObject B hZ K hK (sourceBase B K hK D) V
      (classifier B hZ K hK D) b point
  quasiCompact : QuasiCompact (B.inclusion.map parameter.hom)
  finiteType : LocallyOfFiniteType (B.inclusion.map parameter.hom)

/-- The genuine native finite diagonal constructs the actual pullback
scheme, its true comparison, and its original structural finiteness. -/
theorem exists_data [QuasiCompact (B.inclusion.map V.hom)]
    [LocallyOfFiniteType (B.inclusion.map V.hom)] : Nonempty (Data B hZ K hK D b) := by
  obtain ⟨P,_,e,E,_,hqc,hft,hE,_,_,_,_,_⟩ :=
    NativeCoverFamilyAtlasArrow.exists_finiteType_scheme_and_originalFamilyArrow B hZ K hK
      (sourceBase B K hK D) V (sourceProjection B hZ K hK D)
      (source_schemeCurve B hZ K hK D) b
  exact ⟨⟨P,e,E,hE,hqc,hft⟩⟩

namespace Data

variable {B hZ K hK D b} (E : Data B hZ K hK D b)

abbrev sourceMap : B.inclusion.obj E.parameter.left ⟶ D.parameter :=
  B.inclusion.map E.point.left.left

/-- The original pulled parameter map retains the same ground structure. -/
theorem sourceMap_ground : E.sourceMap ≫ D.structureMap = B.inclusion.map E.parameter.hom := by
  change B.inclusion.map E.point.left.left ≫ B.inclusion.map (sourceBase B K hK D).hom = _
  rw [← Functor.map_comp, Over.w]

instance parameterNoetherian : IsNoetherian (B.inclusion.obj E.parameter.left) := by
  letI := E.quasiCompact
  letI := E.finiteType
  letI : IsLocallyNoetherian (B.inclusion.obj (B.obj hK)) := by
    change IsLocallyNoetherian (Spec (.of K))
    infer_instance
  letI : CompactSpace (B.inclusion.obj (B.obj hK)) := by
    change CompactSpace (Spec (.of K))
    infer_instance
  letI : IsLocallyNoetherian (B.inclusion.obj E.parameter.left) :=
    LocallyOfFiniteType.isLocallyNoetherian (B.inclusion.map E.parameter.hom)
  letI : CompactSpace (B.inclusion.obj E.parameter.left) :=
    QuasiCompact.compactSpace_of_compactSpace (B.inclusion.map E.parameter.hom)
  exact ⟨⟩

instance sourceMapGround_finiteType : LocallyOfFiniteType (E.sourceMap ≫ D.structureMap) := by
  rw [E.sourceMap_ground]
  exact E.finiteType

/-- The unchanged raw original source pullback with its DERIVED actual
cover data. No native source-model isomorphism is supplied. -/
abbrev boundedFamily : BoundedCoverFamily B K :=
  @BoundedCoverFamily.baseChange B K _ D (B.inclusion.obj E.parameter.left)
    E.parameter.left.property E.sourceMap E.parameterNoetherian E.sourceMapGround_finiteType

/-- Its actual Cartesian original curve-family arrow to the original
atlas family, constructed from the true universal comparison. -/
def familyArrow : E.boundedFamily.originalFamily B hZ K ⟶
    NativeCoverFamilyAtlasArrow.targetFamily B hZ K hK V b :=
  NativeCoverFamilyAtlasArrow.familyArrow B hZ K hK (sourceBase B K hK D) V
    (sourceProjection B hZ K hK D) (source_schemeCurve B hZ K hK D) b E.point

/-- The original family arrow preserves the SAME ground structure. -/
theorem familyArrow_ground :
    B.inclusion.map E.familyArrow.baseMap.left ≫
      NativeCoverFamilyAtlasArrow.targetStructure B hZ K hK V b = E.boundedFamily.structureMap :=
  (NativeCoverFamilyAtlasArrow.familyArrow_ground B hZ K hK (sourceBase B K hK D) V
    (sourceProjection B hZ K hK D) (source_schemeCurve B hZ K hK D) b E.point).trans
    E.sourceMap_ground.symm

/-- Every actual native comparison point lifts to this SAME actual
scheme, retaining both of its actual original base maps. -/
theorem covers_native_point {T : BigFppfOver B (Spec (.of K)) hK}
    (F : CoverFamilyStackPullback.PointData B hZ K hK (sourceBase B K hK D) V
      (classifier B hZ K hK D) b (P := T)) :
    ∃ w : T ⟶ E.parameter, w ≫ E.point.left = F.left ∧ w ≫ E.point.right = F.right :=
  CoverFamilyStackPullback.covers_native_point B hZ K hK (sourceBase B K hK D) V
    (classifier B hZ K hK D) b E.equivalence E.point E.universal F

end Data

end M9Native.BoundedCoverAtlasPullback
end
