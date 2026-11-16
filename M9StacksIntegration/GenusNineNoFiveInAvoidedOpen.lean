module

public import M9StacksIntegration.GenusNineFiniteCoverSystem
public import M9StacksIntegration.FiniteBoundedCoverAtlasAvoidance
public import M9StacksIntegration.NativeCoverPointDataOfFieldCurve
public import M9StacksIntegration.PencilProjectiveLineBridge

/-! Actual original atlas curves in an avoided cover-image open have no
degree-five pencil. The physical map, its fixed cover parameter point,
the universal source square, and the native comparison are all derived. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace M9Native.GenusNineNoFiveInAvoidedOpen

open GenusNineBoundedCoverFamilies

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (hK : B.Contains (Spec (.of K)))
  {V : BigFppfOver B (Spec (.of K)) hK}
  (b : Stack.schemeStack.{u,u+1} B (Spec (.of K)) hK V ⟶
    CoverFamilyStackPullback.sourceStack B hZ K hK)
  {m : ℕ} {I : Type v}
  (D : I → GenusNineGroundFieldPolarizedModels.Model.{u} K m)
  (P : ∀ i j, Presentation K B hK (D i) j)

abbrev families : I × Fin 5 → BoundedCoverFamily B K :=
  fun a => (P a.1 a.2).boundedFamily

variable (L : Type u) [Field L] [IsAlgClosed L] [CharZero L]
  (hL : B.Contains (Spec (.of L))) (coefficient : K →+* L)
  (v : NativeGenusNineFieldObjectCurve.fieldBase B K hK L hL coefficient ⟶ V)

abbrev original := NativeCoverPointDataOfFieldCurve.originalCurve B hZ K hK V b
  L hL coefficient v

theorem original_schemeCurve : M9StandaloneDraft.SchemeCurve
    (original B hZ K hK b L hL coefficient v).hom 9 :=
  (NativeGenusNineFieldObjectCurve.model B hZ K hK L hL coefficient
    (NativeCoverPointDataOfFieldCurve.targetObject B hZ K hK V b L hL coefficient v)
    (NativeCoverPointDataOfFieldCurve.targetObject_base B hZ K hK V b L hL coefficient v)).schemeCurve

local instance originalProper : IsProper
    (original B hZ K hK b L hL coefficient v).hom :=
  (original_schemeCurve B hZ K hK b L hL coefficient v).1

local instance originalCurve : IsCurve L
    (original B hZ K hK b L hL coefficient v).hom :=
  (M9StacksIntegration.AllTestSchemeCurveConstants.schemeCurve_field_geometry _
    (original_schemeCurve B hZ K hK b L hL coefficient v)).1

local instance originalSmooth : Smooth
    (original B hZ K hK b L hL coefficient v).hom := by
  letI : SmoothOfRelativeDimension 1
      (original B hZ K hK b L hL coefficient v).hom :=
    (original_schemeCurve B hZ K hK b L hL coefficient v).2.1
  exact SmoothOfRelativeDimension.smooth 1 _

local instance originalConstants : IsIso ((Scheme.ΓSpecIso (.of L)).inv ≫
    (original B hZ K hK b L hL coefficient v).hom.appTop) :=
  (M9StacksIntegration.AllTestSchemeCurveConstants.schemeCurve_field_geometry _
    (original_schemeCurve B hZ K hK b L hL coefficient v)).2.2.1

/-- The actual no-five condition on the exact extracted original curve;
the properness argument is derived from its whole scheme-curve property. -/
def NoFiveAt : Prop :=
  ∀ hd : topologicalKrullDim (original B hZ K hK b L hL coefficient v).left ≤ 1,
    ¬ Nonempty (LinearSeries L
      (original B hZ K hK b L hL coefficient v).hom hd 5 1)

/-- Membership in the actual avoided original target open. -/
abbrev targetPoint : Spec (.of L) ⟶
    B.inclusion.obj (NativeCoverFamilyAtlasArrow.targetFamily B hZ K hK V b).base.left :=
  B.inclusion.map v.left ≫
    eqToHom (BoundedCoverAtlasPointImage.targetBaseEquality B hZ K hK b).symm

/-- Honest original finite model coverage and actual cover-image
avoidance exclude an actual pencil on the exact extracted original
curve. Neither a curve comparison nor graph membership is an input. -/
theorem noFive_of_avoids_comparisonPoints
    (hcov : GenusNineFiniteCoverSystem.CoversOriginalCurves K D)
    (U : (B.inclusion.obj
      (NativeCoverFamilyAtlasArrow.targetFamily B hZ K hK V b).base.left).Opens)
    (havoid : ∀ (a : I × Fin 5) (T : BigFppfOver B (Spec (.of K)) hK)
      (F : CoverFamilyStackPullback.PointData B hZ K hK
        (BoundedCoverAtlasPullback.sourceBase B K hK (families (B := B) (K := K) (hK := hK) (D := D) (P := P) a)) V
        (BoundedCoverAtlasPullback.classifier B hZ K hK (families (B := B) (K := K) (hK := hK) (D := D) (P := P) a)) b
        (P := T)) (t : B.inclusion.obj T.left),
        BoundedCoverAtlasPointImage.targetPoint B hZ K hK (families (B := B) (K := K) (hK := hK) (D := D) (P := P) a) b F t ∉ U)
    (hpoint : targetPoint B hZ K hK b L hL coefficient v (IsLocalRing.closedPoint L) ∈ U)
    (hd : topologicalKrullDim (original B hZ K hK b L hL coefficient v).left ≤ 1) :
    ¬ Nonempty (LinearSeries L
      (original B hZ K hK b L hL coefficient v).hom hd 5 1) := by
  rintro ⟨A⟩
  obtain ⟨g,hg,hnc,_,hdeg,_⟩ :=
    PencilProjectiveLineBridge.exists_finite_map_degree_one_to_five
      (original B hZ K hK b L hL coefficient v).hom hd A
  have hgen := (M9StacksIntegration.AllTestSchemeCurveConstants.schemeCurve_field_geometry _
    (original_schemeCurve B hZ K hK b L hL coefficient v)).2.2.2
  obtain ⟨i,j,a,r,sq⟩ := GenusNineFiniteCoverSystem.exists_universal_source_point
    K B hK D P hcov L hL coefficient
    (original B hZ K hK b L hL coefficient v).left
    (original B hZ K hK b L hL coefficient v).hom hgen g hg hnc hdeg
  have sq' : IsPullback r (original B hZ K hK b L hL coefficient v).hom
      ((BigFppfOver.toScheme B integerBase hZ).map
        (X := BoundedCoverAtlasPullback.sourceTotal B hZ K (P i j).boundedFamily)
        (Y := (Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj
          (BoundedCoverAtlasPullback.sourceBase B K hK (P i j).boundedFamily))
        (BoundedCoverAtlasPullback.sourceProjection B hZ K hK (P i j).boundedFamily))
      ((BigFppfOver.toScheme B integerBase hZ).map
        (X := (Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj
          (NativeGenusNineFieldObjectCurve.fieldBase B K hK L hL coefficient))
        (Y := (Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj
          (BoundedCoverAtlasPullback.sourceBase B K hK (P i j).boundedFamily))
        ((Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).map a)) := by
    change IsPullback r (original B hZ K hK b L hL coefficient v).hom
      (P i j).boundedFamily.projection (B.inclusion.map a.left)
    exact sq
  let F := NativeCoverPointDataOfFieldCurve.pointData B hZ K hK
    (BoundedCoverAtlasPullback.sourceBase B K hK (P i j).boundedFamily) V
    (Z := BoundedCoverAtlasPullback.sourceTotal B hZ K (P i j).boundedFamily)
    (BoundedCoverAtlasPullback.sourceProjection B hZ K hK (P i j).boundedFamily)
    (BoundedCoverAtlasPullback.source_schemeCurve B hZ K hK (P i j).boundedFamily)
    b L hL coefficient v a r sq'
  have hbad := havoid (i,j)
    (NativeGenusNineFieldObjectCurve.fieldBase B K hK L hL coefficient) F
    (IsLocalRing.closedPoint L)
  have hright : F.right = v :=
    NativeCoverPointDataOfFieldCurve.pointData_right B hZ K hK
      (BoundedCoverAtlasPullback.sourceBase B K hK (P i j).boundedFamily) V
      (Z := BoundedCoverAtlasPullback.sourceTotal B hZ K (P i j).boundedFamily)
      (BoundedCoverAtlasPullback.sourceProjection B hZ K hK (P i j).boundedFamily)
      (BoundedCoverAtlasPullback.source_schemeCurve B hZ K hK (P i j).boundedFamily)
      b L hL coefficient v a r sq'
  have hpEq : BoundedCoverAtlasPointImage.targetPoint B hZ K hK
      (P i j).boundedFamily b F = targetPoint B hZ K hK b L hL coefficient v := by
    change B.inclusion.map F.right.left ≫
        eqToHom (BoundedCoverAtlasPointImage.targetBaseEquality B hZ K hK b).symm =
      B.inclusion.map v.left ≫
        eqToHom (BoundedCoverAtlasPointImage.targetBaseEquality B hZ K hK b).symm
    rw [hright]
  apply hbad
  rw [hpEq]
  exact hpoint

include P

/-- The actual finite cover families construct a dense open on a true
integral smooth-classifier chart, and every original algebraically
closed field point in that open has no degree-five pencil. -/
theorem exists_dense_open_noFive [Finite I]
    [QuasiCompact (B.inclusion.map V.hom)] [LocallyOfFiniteType (B.inclusion.map V.hom)]
    [IsIntegral (B.inclusion.obj
      (NativeCoverFamilyAtlasArrow.targetFamily B hZ K hK V b).base.left)]
    [LocallyOfFiniteType (NativeCoverFamilyAtlasArrow.targetStructure B hZ K hK V b)]
    (hR : Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (CurveFieldClassifyingFamily.stackMorphism B hZ hK
        (curvesFiberedCategory_isAlgebraicStack.{u,u+1} B hZ)
        (NativeCoverFamilyAtlasArrow.targetFamily B hZ K hK V b)
        (NativeCoverFamilyAtlasArrow.targetStructure B hZ K hK V b)))
    (hcov : GenusNineFiniteCoverSystem.CoversOriginalCurves K D) :
    ∃ U : (B.inclusion.obj
      (NativeCoverFamilyAtlasArrow.targetFamily B hZ K hK V b).base.left).Opens,
      Dense (U : Set (B.inclusion.obj
        (NativeCoverFamilyAtlasArrow.targetFamily B hZ K hK V b).base.left)) ∧
      (U : Set (B.inclusion.obj
        (NativeCoverFamilyAtlasArrow.targetFamily B hZ K hK V b).base.left)).Nonempty ∧
      ∀ (L : Type u) [Field L] [IsAlgClosed L] [CharZero L]
        (hL : B.Contains (Spec (.of L))) (coefficient : K →+* L)
        (v : NativeGenusNineFieldObjectCurve.fieldBase B K hK L hL coefficient ⟶ V),
        targetPoint B hZ K hK b L hL coefficient v (IsLocalRing.closedPoint L) ∈ U →
        NoFiveAt B hZ K hK b L hL coefficient v := by
  obtain ⟨U,hd,hn,ha⟩ :=
    FiniteBoundedCoverAtlasAvoidance.exists_dense_open_avoiding_comparisonPoints
      B hZ K hK b hR (families (B := B) (K := K) (hK := hK) (D := D) (P := P))
  refine ⟨U,hd,hn,?_⟩
  intro L _ _ _ hL coefficient v hp hd
  exact noFive_of_avoids_comparisonPoints B hZ K hK b D P L hL coefficient v
    hcov U ha hp hd

end M9Native.GenusNineNoFiveInAvoidedOpen
end
