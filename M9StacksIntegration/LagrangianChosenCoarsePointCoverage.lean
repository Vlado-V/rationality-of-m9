module

public import M9StacksIntegration.NativeGenusNineNoFivePoints
public import M9StacksIntegration.NativeClassifierPointRange
public import M9StacksIntegration.LagrangianChosenCoarseFamily
public import M9StacksIntegration.GenusNineMukaiCrossField
public import M9StacksIntegration.NativeSmoothGenusPhysicalCoarseMap

@[expose] public section

/-! Actual image coverage of original no-five-pencil curve representatives.
The genuine Mukai fibre isomorphism constructs the good-family point.
The proved physical-to-coarse comparison constructs equality on the SAME
chosen coarse space. Point-map compatibility then places the source image
in the range of that SAME chosen coarse map.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.LagrangianChosenCoarsePointCoverage
open NativeGenusNineNoFivePoints NativeStackCoverageDenseImage
open M9StacksIntegration.AllTestSchemeCurveConstants
open LagrangianLinearSections LagrangianLinearSectionGenericSmooth

attribute [local implicit_reducible] AlgebraicGeometry.schemeOverIntegers
  NativeGenusNineNoFivePoints.CurveDatum.base
  NativeGenusNineNoFivePoints.CurveDatum.classifier
  NativeGenusNineNoFivePoints.CurveDatum.identityPoint
  NativeGenusNineNoFivePoints.CurveDatum.fieldPoint
  NativeGenusNineNoFivePoints.CurveDatum.nativePoint

theorem nine_ge_two : 2 ≤ 9 := by decide

universe u
variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K)))
  (hZ : B.Contains integerBase)

/-- Every actual ACL original no-five curve datum is an actual point in
the image of the original Lagrangian family's chosen coarse map. -/
theorem curveDatum_coarsePoint_mem_range (d : CurveDatum B hZ K hK) :
    coarsePointMap B (Spec (.of K)) hK
        (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ K hK 9 nine_ge_two)
        d.nativePoint ∈
      Set.range (Space.pointsMap B (Spec (.of K)) hK
        (schemeSpace (LagrangianNativeGenusNineFamily.base K B hK)).obj
        (LagrangianChosenCoarseFamily.nativeMap K B hK hZ).hom) := by
  let f := (BigFppfOver.toScheme B integerBase hZ).map d.projection
  let : IsProper f := d.schemeCurve.1
  let : SmoothOfRelativeDimension 1 f := d.schemeCurve.2.1
  let : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  let : IsCurve d.carrier f := (schemeCurve_field_geometry f d.schemeCurve).1
  have hg : genus f = 9 := (schemeCurve_field_geometry f d.schemeCurve).2.2.2
  obtain ⟨p, e, hp, he⟩ :=
    GenusNineMukaiCrossField.exists_original_goodFibreIso d.coefficient f hg d.noFive
  let a : d.base ⟶ LagrangianNativeGenusNineFamily.base K B hK :=
    Over.homMk (ObjectProperty.homMk p) (ObjectProperty.hom_ext _ hp)
  let c : B.obj hK ⟶ B.obj hZ := NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK
  let a₀ := (Over.map c).map (𝟙 d.base)
  let a₁ := (Over.map c).map a
  let q₁ := LagrangianNativeGenusNineFamily.integerProjection K B hK hZ
  have ha₀ : a₀ = 𝟙 ((Over.map c).obj d.base) := (Over.map c).map_id d.base
  have hb₀ : (BigFppfOver.toScheme B integerBase hZ).map a₀ = 𝟙 (Spec (.of d.carrier)) :=
    (congrArg (BigFppfOver.toScheme B integerBase hZ).map ha₀).trans
      ((BigFppfOver.toScheme B integerBase hZ).map_id ((Over.map c).obj d.base))
  let : IsIso ((BigFppfOver.toScheme B integerBase hZ).map a₀) :=
    ((BigFppfOver.toScheme B integerBase hZ).mapIso
      ((Over.map c).mapIso (Iso.refl d.base))).isIso_hom
  let ep : pullback ((BigFppfOver.toScheme B integerBase hZ).map d.projection)
        ((BigFppfOver.toScheme B integerBase hZ).map a₀) ≅
      pullback ((BigFppfOver.toScheme B integerBase hZ).map q₁)
        ((BigFppfOver.toScheme B integerBase hZ).map a₁) :=
    asIso (pullback.fst f ((BigFppfOver.toScheme B integerBase hZ).map a₀)) ≪≫ e
  have hep : ep.hom ≫ pullback.snd
      ((BigFppfOver.toScheme B integerBase hZ).map q₁)
      ((BigFppfOver.toScheme B integerBase hZ).map a₁) =
    pullback.snd ((BigFppfOver.toScheme B integerBase hZ).map d.projection)
      ((BigFppfOver.toScheme B integerBase hZ).map a₀) := by
    change (pullback.fst f ((BigFppfOver.toScheme B integerBase hZ).map a₀) ≫ e.hom) ≫
      pullback.snd (restrictedProjection K) p = _
    rw [Category.assoc, he]
    calc
      pullback.fst f ((BigFppfOver.toScheme B integerBase hZ).map a₀) ≫ f =
          pullback.snd f ((BigFppfOver.toScheme B integerBase hZ).map a₀) ≫
            ((BigFppfOver.toScheme B integerBase hZ).map a₀) := pullback.condition
      _ = _ :=
        (congrArg (fun t : Spec (.of d.carrier) ⟶ Spec (.of d.carrier) =>
          pullback.snd f ((BigFppfOver.toScheme B integerBase hZ).map a₀) ≫ t) hb₀).trans
            (Category.comp_id _)
  let g₀ := ASClassifierGeometricLift.nativeMap B (Spec (.of K)) hK
    (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ K hK 9 nine_ge_two) d.classifier
  let g₁ := LagrangianChosenCoarseFamily.nativeMap K B hK hZ
  have hm : g₀ = schemeSpaceMap a ≫ g₁ := by
    have h := NativeSmoothGenusPhysicalCoarseMap.classifyingMaps_eq_of_physicalIso
      B hZ K hK 9 nine_ge_two d.projection q₁ d.schemeCurve
        (LagrangianNativeGenusNineFamily.original_schemeCurve K B hK hZ)
        (𝟙 d.base) a ep hep
    change schemeSpaceMap (𝟙 d.base) ≫ g₀ = schemeSpaceMap a ≫ g₁ at h
    have hl : schemeSpaceMap (𝟙 d.base) ≫ g₀ = g₀ :=
      (congrArg (fun m : schemeSpace d.base ⟶ schemeSpace d.base => m ≫ g₀)
        ((schemeSpaceFunctor B (Spec (.of K)) hK).map_id d.base)).trans
          (Category.id_comp g₀)
    exact hl.symm.trans h
  exact NativeClassifierPointRange.mem_range_of_nativeMap_factorization
    B (Spec (.of K)) hK
    (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ K hK 9 nine_ge_two)
    d.classifier (LagrangianChosenCoarseFamily.fieldClassifier K B hK hZ) a hm d.identityPoint

/-- Actual point coverage of the no-five representative locus is a
conclusion of the original curve theorem and the native arrow constructions. -/
theorem noFiveLocus_coarsePoint_coverage :
    ∀ z ∈ locus B hZ K hK,
      coarsePointMap B (Spec (.of K)) hK
          (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ K hK 9 nine_ge_two) z ∈
        Set.range (Space.pointsMap B (Spec (.of K)) hK
          (schemeSpace (LagrangianNativeGenusNineFamily.base K B hK)).obj
          (LagrangianChosenCoarseFamily.nativeMap K B hK hZ).hom) := by
  rintro _ ⟨d, rfl⟩
  exact curveDatum_coarsePoint_mem_range K B hK hZ d

/-- The only remaining geometric input here is the separately proved
density of actual no-five representatives in the original source stack. -/
theorem denseRange_of_dense_noFiveLocus
    (hd : @Dense _ (Stack.pointTopology B (Spec (.of K)) hK
      (M9StacksIntegration.GenusNineCoarseOverField.smoothStack
        B hZ K hK 9 nine_ge_two).val) (locus B hZ K hK)) :
    @DenseRange _ (Space.pointTopology B (Spec (.of K)) hK
      (LagrangianChosenCoarseFamily.target K B hK hZ).obj) _
      (Space.pointsMap B (Spec (.of K)) hK
        (schemeSpace (LagrangianNativeGenusNineFamily.base K B hK)).obj
        (LagrangianChosenCoarseFamily.nativeMap K B hK hZ).hom) :=
  denseRange_of_point_coverage B (Spec (.of K)) hK
    (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ K hK 9 nine_ge_two)
    (M9StacksIntegration.GenusNineCoarseOverField.coarseMap_universalHomeomorphism
      B hZ K hK 9 nine_ge_two)
    (LagrangianChosenCoarseFamily.nativeMap K B hK hZ) (locus B hZ K hK) hd
      (noFiveLocus_coarsePoint_coverage K B hK hZ)

end M9Native.LagrangianChosenCoarsePointCoverage
