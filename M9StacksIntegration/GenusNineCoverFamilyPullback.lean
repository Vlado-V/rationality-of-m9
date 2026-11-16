module

public import M9StacksIntegration.NativeCoverFamilyAtlasArrow
public import M9StacksIntegration.GenusNineIntegralAtlas
public import M9StacksIntegration.AtlasFamilyClassifierComparison

@[expose] public section

/-!
# Actual cover-family pullbacks to actual integral genus-nine atlas components

The target is the chosen native atlas component, and its original curve
family is the actual unit-value projection. Its integral base, original
field structure and smooth literal family classifier are derived. The
source is a genuine original schematic genus-nine family. No algebraicity,
finite-diagonal, target-integrality, classifier-smoothness or family-arrow
premise is supplied.

This is a new legacy consumer because the checked actual atlas consumes
frozen legacy source-property producers.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace M9Native.GenusNineCoverFamilyPullback

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

private def transportedStructure {R Q : CurveFamily B hZ} (e : R = Q)
    (s : B.inclusion.obj R.base.left ⟶ Spec (.of K)) :
    B.inclusion.obj Q.base.left ⟶ Spec (.of K) :=
  eqToHom (congrArg (fun F : CurveFamily B hZ => B.inclusion.obj F.base.left) e.symm) ≫ s

private theorem fieldBase_transport {R Q : CurveFamily B hZ} (e : R = Q)
    (s : B.inclusion.obj R.base.left ⟶ Spec (.of K)) :
    CurveFieldClassifyingFamily.fieldBase B hZ hK Q (transportedStructure B hZ K e s) =
      CurveFieldClassifyingFamily.fieldBase B hZ hK R s := by
  cases e
  simp only [transportedStructure, eqToHom_refl, Category.id_comp]

private theorem structure_unique (R : CurveFamily B hZ)
    (s t : B.inclusion.obj R.base.left ⟶ Spec (.of K))
    (V : BigFppfOver B (Spec (.of K)) hK)
    (hs : CurveFieldClassifyingFamily.fieldBase B hZ hK R s = V)
    (ht : CurveFieldClassifyingFamily.fieldBase B hZ hK R t = V) : s = t := by
  have h := congrArg (Over.post B.inclusion).obj (hs.trans ht.symm)
  change Over.mk s = Over.mk t at h
  simpa only [Over.eqToHom_left, eqToHom_refl, Category.id_comp,
    Over.mk_left, Over.mk_hom] using
    (Over.w (eqToHom h)).symm

private theorem classifier_smooth_transport {R Q : CurveFamily B hZ} (e : R = Q)
    (s : B.inclusion.obj R.base.left ⟶ Spec (.of K))
    (hs : Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (CurveFieldClassifyingFamily.stackMorphism B hZ hK
        (AtlasFamilyClassifierComparison.actualAlgebraicity B hZ) R s)) :
    Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (CurveFieldClassifyingFamily.stackMorphism B hZ hK
        (AtlasFamilyClassifierComparison.actualAlgebraicity B hZ) Q
        (transportedStructure B hZ K e s)) := by
  cases e
  have ht : transportedStructure B hZ K (rfl : R = R) s = s := by
    simp only [transportedStructure, eqToHom_refl, Category.id_comp]
  exact (congrArg (fun t : B.inclusion.obj R.base.left ⟶ Spec (.of K) =>
    Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (CurveFieldClassifyingFamily.stackMorphism B hZ hK
        (AtlasFamilyClassifierComparison.actualAlgebraicity B hZ) R t)) ht).mpr hs

abbrev targetSite (x : GenusNineIntegralAtlas.atlasScheme B hZ K hK) :=
  GenusNineIntegralAtlas.componentSite B hZ K hK x

abbrev targetMap (x : GenusNineIntegralAtlas.atlasScheme B hZ K hK) :=
  GenusNineIntegralAtlas.componentMap B hZ K hK x

/-- The same original curve family used by the actual universal comparison. -/
abbrev targetFamily (x : GenusNineIntegralAtlas.atlasScheme B hZ K hK) :=
  NativeCoverFamilyAtlasArrow.targetFamily B hZ K hK (targetSite B hZ K hK x)
    (targetMap B hZ K hK x)

abbrev targetStructure (x : GenusNineIntegralAtlas.atlasScheme B hZ K hK) :=
  NativeCoverFamilyAtlasArrow.targetStructure B hZ K hK (targetSite B hZ K hK x)
    (targetMap B hZ K hK x)

/-- Its field-site base is the literal original atlas component. -/
theorem target_fieldBase (x : GenusNineIntegralAtlas.atlasScheme B hZ K hK) :
    CurveFieldClassifyingFamily.fieldBase B hZ hK (targetFamily B hZ K hK x)
      (targetStructure B hZ K hK x) = targetSite B hZ K hK x := by
  apply Deformation.Artin.post_obj_injective
  change Over.mk (targetStructure B hZ K hK x) = _
  exact Over.mk_eqToHom_comp _ _

/-- Integrality is that of the actual open atlas component, not a premise. -/
theorem target_integral (x : GenusNineIntegralAtlas.atlasScheme B hZ K hK) :
    IsIntegral (B.inclusion.obj (targetFamily B hZ K hK x).base.left) := by
  change IsIntegral (B.inclusion.obj (CurveFieldClassifyingFamily.fieldBase B hZ hK
    (targetFamily B hZ K hK x) (targetStructure B hZ K hK x)).left)
  rw [target_fieldBase]
  exact GenusNineIntegralAtlas.component_integral B hZ K hK x

theorem target_structural_properties (x : GenusNineIntegralAtlas.atlasScheme B hZ K hK) :
    Smooth (targetStructure B hZ K hK x) ∧
      QuasiCompact (targetStructure B hZ K hK x) ∧
      LocallyOfFiniteType (targetStructure B hZ K hK x) := by
  change Smooth (B.inclusion.map (CurveFieldClassifyingFamily.fieldBase B hZ hK
      (targetFamily B hZ K hK x) (targetStructure B hZ K hK x)).hom) ∧
    QuasiCompact (B.inclusion.map (CurveFieldClassifyingFamily.fieldBase B hZ hK
      (targetFamily B hZ K hK x) (targetStructure B hZ K hK x)).hom) ∧
    LocallyOfFiniteType (B.inclusion.map (CurveFieldClassifyingFamily.fieldBase B hZ hK
      (targetFamily B hZ K hK x) (targetStructure B hZ K hK x)).hom)
  rw [target_fieldBase]
  exact GenusNineIntegralAtlas.component_structural_properties B hZ K hK x

/-- The literal classifier of this SAME original target family is smooth. -/
theorem target_classifier_smooth (x : GenusNineIntegralAtlas.atlasScheme B hZ K hK) :
    Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (CurveFieldClassifyingFamily.stackMorphism B hZ hK
        (AtlasFamilyClassifierComparison.actualAlgebraicity B hZ)
        (targetFamily B hZ K hK x) (targetStructure B hZ K hK x)) := by
  let b := targetMap B hZ K hK x
  let R := AtlasFamilyClassifierComparison.atlasFamily B hZ K hK 9 (by decide) b
  let s := AtlasFamilyClassifierComparison.atlasStructure B hZ K hK 9 (by decide) b
  have he : R = targetFamily B hZ K hK x :=
    AtlasFamilyClassifierComparison.atlasFamily_eq_nativeProjection B hZ K hK 9
      (by decide) b
  have hs : CurveFieldClassifyingFamily.fieldBase B hZ hK R s = targetSite B hZ K hK x :=
    AtlasFamilyClassifierComparison.atlasFamily_fieldBase B hZ K hK 9 (by decide) b
  have hst : transportedStructure B hZ K he s = targetStructure B hZ K hK x :=
    structure_unique B hZ K hK (targetFamily B hZ K hK x) _ _ _
      ((fieldBase_transport B hZ K hK he s).trans hs) (target_fieldBase B hZ K hK x)
  have hsm := classifier_smooth_transport B hZ K hK he s
    (AtlasFamilyClassifierComparison.atlasClassifier_isSmooth B hZ K hK 9
      (by decide) b (GenusNineIntegralAtlas.component_smooth B hZ K hK x))
  exact (congrArg
    (fun t : B.inclusion.obj (targetFamily B hZ K hK x).base.left ⟶ Spec (.of K) =>
      Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
        (CurveFieldClassifyingFamily.stackMorphism B hZ hK
          (AtlasFamilyClassifierComparison.actualAlgebraicity B hZ)
          (targetFamily B hZ K hK x) t)) hst).mp hsm

variable (Y : BigFppfOver B (Spec (.of K)) hK)
  {Z : BigFppfOver B integerBase hZ}
  (q : Z ⟶ (NativeCoverFamilyAtlasArrow.integerBaseFunctor B hZ K hK).obj Y)
  (hq : M9StandaloneDraft.SchemeCurve ((BigFppfOver.toScheme B integerBase hZ).map q) 9)
  [QuasiCompact (B.inclusion.map Y.hom)] [LocallyOfFiniteType (B.inclusion.map Y.hom)]

/-- An actual finite-type scheme representing the cover-family pullback to
this actual integral component, with its real original family arrow. -/
theorem exists_pullback (x : GenusNineIntegralAtlas.atlasScheme B hZ K hK) :
    ∃ (P : BigFppfOver B (Spec (.of K)) hK)
      (qP : P ⟶ FiniteDiagonalSchemePullback.productSite B (Spec (.of K)) hK Y
        (targetSite B hZ K hK x))
      (e : StacksRepresentableCFG.EquivalenceOver (Over.forget P)
        (CoverFamilyStackPullback.pairProjection B hZ K hK Y (targetSite B hZ K hK x)
          (NativeCoverFamilyAtlasArrow.sourceClassifier B hZ K hK Y q hq)
          (targetMap B hZ K hK x)))
      (D : CoverFamilyStackPullback.PointData B hZ K hK Y (targetSite B hZ K hK x)
        (NativeCoverFamilyAtlasArrow.sourceClassifier B hZ K hK Y q hq)
        (targetMap B hZ K hK x) (P := P)),
      IsFinite ((BigFppfOver.toScheme B (Spec (.of K)) hK).map qP) ∧
      QuasiCompact (B.inclusion.map P.hom) ∧
      LocallyOfFiniteType (B.inclusion.map P.hom) ∧
      e.hom.functor.obj (Over.mk (𝟙 P)) =
        CoverFamilyStackPullback.pointObject B hZ K hK Y (targetSite B hZ K hK x)
          (NativeCoverFamilyAtlasArrow.sourceClassifier B hZ K hK Y q hq)
          (targetMap B hZ K hK x) D ∧
      B.inclusion.map (NativeCoverFamilyAtlasArrow.familyArrow B hZ K hK Y
          (targetSite B hZ K hK x) q hq (targetMap B hZ K hK x) D).baseMap.left ≫
        targetStructure B hZ K hK x = B.inclusion.map P.hom ∧
      QuasiCompact (B.inclusion.map D.right.left) ∧
      LocallyOfFiniteType (B.inclusion.map D.right.left) ∧
      QuasiCompact (B.inclusion.map (NativeCoverFamilyAtlasArrow.familyArrow B hZ K hK Y
        (targetSite B hZ K hK x) q hq (targetMap B hZ K hK x) D).baseMap.left) ∧
      LocallyOfFiniteType (B.inclusion.map (NativeCoverFamilyAtlasArrow.familyArrow B hZ K hK Y
        (targetSite B hZ K hK x) q hq (targetMap B hZ K hK x) D).baseMap.left) := by
  have hp := GenusNineIntegralAtlas.component_structural_properties B hZ K hK x
  have : QuasiCompact (B.inclusion.map (targetSite B hZ K hK x).hom) := hp.2.1
  have : LocallyOfFiniteType (B.inclusion.map (targetSite B hZ K hK x).hom) := hp.2.2
  exact NativeCoverFamilyAtlasArrow.exists_finiteType_scheme_and_originalFamilyArrow
    B hZ K hK Y (targetSite B hZ K hK x) q hq (targetMap B hZ K hK x)

end M9Native.GenusNineCoverFamilyPullback
