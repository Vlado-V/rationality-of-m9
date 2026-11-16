module

public import M9StacksIntegration.AllTestNativeOriginalCurveCharts
public import M9StacksIntegration.AllTestNativeFieldSchemeModel
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyEtaleSchemeChartsProof

/-!
# Actual original all-test family from an intrinsic native genus family

The factory invokes the pinned, kernel-checked native0E6F theorem
hasEtaleLocalSchemeCharts; that assertion is not a premise.
The resulting total may be nonschematic. The literal original local curve
condition includes ALL original extension fields, without a cutoff premise.
No original family/classifier/equivalence or geometry is an argument.

The base-equality bookkeeping below is the actual proof from pinned
Quot/CurveFamilySchemeGlue, renamed locally to avoid its unrelated imports.
The original native source is untouched.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestNativeOriginalFamily
open AllTestNativeCurveFamily AllTestNativeCoefficientProjection
  AllTestNativeCoefficientSchemes AllTestNativeOriginalCurveCharts
  AllTestBoundedCharts AllTestNativeRepresentedCurveGeometry
universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

abbrev familyOfBaseEq (F : CurveFamily B hZ)
    {V : BigFppfOver B integerBase hZ} (e : F.base = V) : CurveFamily B hZ where
  base := V
  total := F.total
  toBase := F.toBase ≫ eqToHom (congrArg schemeSpace e)
  flat := by subst e; simpa using F.flat
  proper := by subst e; simpa using F.proper
  finitePresentation := by subst e; simpa using F.finitePresentation
  relativeDimensionLE := by subst e; simpa using F.relativeDimensionLE

def familyOfBaseEqIso (F : CurveFamily B hZ)
    {V : BigFppfOver B integerBase hZ} (e : F.base = V) : familyOfBaseEq B hZ F e ≅ F :=
  AllTestNativeFieldSchemeModel.isoMk
    (F := familyOfBaseEq B hZ F e) (G := F) (eqToIso e.symm) (Iso.refl _) (by
    subst e
    change 𝟙 _ ≫ F.toBase = (F.toBase ≫ 𝟙 _) ≫ schemeSpaceMap (𝟙 F.base)
    rw [show schemeSpaceMap (𝟙 F.base) = 𝟙 _ from
      (schemeSpaceFunctor B integerBase hZ).map_id _]
    simp)

/-- Intrinsic native membership constructs the actual literal ORIGINAL
family, over the SAME original base and coefficient map. Genuine0E6F
constructs all local charts; their full original curve predicate is proved. -/
def originalFamily
    (T : BigFppfOver B (Spec (.of K)) hK) (F : CurveFamily B hZ)
    (hbase : F.base = nativeBase B hZ K hK T) (g : ℕ)
    (hF : IsSmoothH0FamilyOfFibreGenus B hZ g F) :
    M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g := by
  let k := fieldToInteger B hZ K hK
  let N := familyOfBaseEq B hZ F hbase
  have hN : IsSmoothH0FamilyOfFibreGenus B hZ g N :=
    CurveFamily.isSmoothH0FamilyOfFibreGenus_of_hom (familyOfBaseEqIso B hZ F hbase).hom hF
  let π : N.total.obj ⟶ yoneda.obj ((Over.map k).obj T) := N.toBase.hom
  refine
    { total := originalTotal K B hZ hK T π
      projection := originalProjection K B hZ hK T π
      locally_curve := ?_ }
  intro t
  obtain ⟨U, Z, a, q, p, he, ht, hcart⟩ :=
    C1590Private.hasEtaleLocalSchemeCharts B hZ N t
  let U₀ := schemeLift B (Spec (.of K)) integerBase hK hZ k a
  let Z₀ := schemeLift B (Spec (.of K)) integerBase hK hZ k (q ≫ a)
  let v₀ : U₀ ⟶ T := schemeLiftBaseMap B (Spec (.of K)) integerBase hK hZ k a
  let q₀ : Z₀ ⟶ U₀ := schemeLiftMap B (Spec (.of K)) integerBase hK hZ k a q
  let p₀ : yoneda.obj ((Over.map k).obj Z₀) ⟶ N.total.obj :=
    yoneda.map (schemeLiftIso B (Spec (.of K)) integerBase hK hZ k (q ≫ a)).hom ≫ p.hom
  have hcart₀ : IsPullback p₀ (yoneda.map ((Over.map k).map q₀))
      π (yoneda.map ((Over.map k).map v₀)) :=
    schemeLift_chart_isPullback B (Spec (.of K)) integerBase hK hZ k π a q p.hom
      (AlgebraicSpaces.isPullback_hom B integerBase hZ hcart)
  refine ⟨(boundedInclusion B K hK).obj U₀, (boundedInclusion B K hK).obj Z₀,
    (boundedInclusion B K hK).map v₀, (boundedInclusion B K hK).map q₀,
    originalCurveChart K B hZ hK π q₀ v₀ p₀ hcart₀, he, ht,
    originalCurveChart_isPullback K B hZ hK π q₀ v₀ p₀ hcart₀, ?_⟩
  exact schemeCurve_of_native_chart B hZ N g hN q a p hcart

set_option backward.defeqAttrib.useBackward true in
/-- The constructed FULL ORIGINAL family recovers the actual native family,
including its SAME projection and base identification. No comparison is assumed. -/
def originalFamilyNativeIso
    (T : BigFppfOver B (Spec (.of K)) hK) (F : CurveFamily B hZ)
    (hbase : F.base = nativeBase B hZ K hK T) (g : ℕ)
    (hF : IsSmoothH0FamilyOfFibreGenus B hZ g F) :
    nativeCurveFamily B hZ K hK (originalFamily B hZ K hK T F hbase g hF) ≅ F := by
  let k := fieldToInteger B hZ K hK
  let N := familyOfBaseEq B hZ F hbase
  let π : N.total.obj ⟶ yoneda.obj ((Over.map k).obj T) := N.toBase.hom
  let G := originalFamily B hZ K hK T F hbase g hF
  let NG := nativeCurveFamily B hZ K hK G
  let ep : NG.total.obj ≅ N.total.obj := originalTotalRelocalizeIso K B hZ hK T π
  let e : NG.total ≅ N.total := (ObjectProperty.fullyFaithfulι _).preimageIso ep
  let E : NG ≅ N := by
    apply AllTestNativeFieldSchemeModel.isoMk (F := NG) (G := N)
      (Iso.refl (nativeBase B hZ K hK T)) e
    apply ObjectProperty.hom_ext
    change ep.hom ≫ π =
      ((OverShriek.relocalizePresheafFunctor k).map
        (AllTestBoundedCartesian.baseMap K B hK T G.projection) ≫
        (relocalizedYonedaIso B (B.obj hK) (B.obj hZ) k T).hom) ≫
        yoneda.map (𝟙 (nativeBase B hZ K hK T))
    rw [(yoneda (C := BigFppfOver B integerBase hZ)).map_id, Category.comp_id]
    exact originalProjection_relocalize K B hZ hK T π
  exact E ≪≫ familyOfBaseEqIso B hZ F hbase

/-- The original coefficient and base are retained literally, with no
unmentioned automorphism in the recovery isomorphism. -/
theorem originalFamilyNativeIso_baseMap
    (T : BigFppfOver B (Spec (.of K)) hK) (F : CurveFamily B hZ)
    (hbase : F.base = nativeBase B hZ K hK T) (g : ℕ)
    (hF : IsSmoothH0FamilyOfFibreGenus B hZ g F) :
    (originalFamilyNativeIso B hZ K hK T F hbase g hF).hom.baseMap =
      eqToHom hbase.symm := by
  change 𝟙 (nativeBase B hZ K hK T) ≫ eqToHom hbase.symm = eqToHom hbase.symm
  exact Category.id_comp _

end M9StacksIntegration.AllTestNativeOriginalFamily
