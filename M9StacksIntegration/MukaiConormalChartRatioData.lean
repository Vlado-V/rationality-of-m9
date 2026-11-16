module

public import M9StacksIntegration.MukaiConormalChartDifferential
public import M9StacksIntegration.MukaiConormalChartFrame
public import M9StacksIntegration.MukaiConormalCoefficientImage
public import M9StacksIntegration.ProjectiveRatioFieldDifferential

/-! All ratio and differential data for the original native conormal
image are derived from the actual chart, original determinant frame and
native universal derivations. No image or first-jet conclusion is input. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module TopologicalSpace
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

namespace M9Native.MukaiConormalChartRatioData

open LagrangianGrassmannian LagrangianPlucker LagrangianPluckerQuotient
open MukaiConormalChartJets

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse
attribute [local instance_reducible] ProjectiveSpectrum.top

variable (K : Type u) [Field K] [CharZero K] [IsAlgClosed K]
variable (f : chart K ⟶ space K) [Etale f]
variable (hf : f ≫ projection K = chartProjection K)
variable (z : Spec (.of K) ⟶ chart K)
variable (e : (Scheme.Modules.pullback f).obj (determinantLine K) ≅
  SheafOfModules.unit (chart K).ringCatSheaf)

abbrev point := z ≫ f
abbrev projectivePoint := (z ≫ f) ≫ integralPrimitivePlucker K
abbrev tuple := MukaiConormalChartFrame.sectionTuple K f e
abbrev pointFrame := MukaiConormalChartFrame.pointDeterminantFrame K f e z

abbrev PivotCondition (i : Fin 14) :=
  ProjectiveEulerFieldPoint.image (ULift.{u} ℤ) 13 K (projectivePoint K f z) ∈
    ProjectiveSpectrum.basicOpen (polyGrading (ULift.{u} ℤ) 13) (MvPolynomial.X i)

abbrev pointRatio (i : Fin 14) (hp : PivotCondition K f z i) : Fin 14 → K :=
  ProjectiveEulerFieldPoint.ratio (ULift.{u} ℤ) 13 K (projectivePoint K f z) i hp

abbrev pointBasis (i : Fin 14) (hp : PivotCondition K f z i) :=
  MukaiEulerFieldPoint.basis K (point K f z) (pointFrame K f z e) i hp

def inputDifferential : MukaiEulerFieldPoint.Source K (point K f z) →ₗ[K] PointCotangent K z :=
  (MukaiConormalChartDifferential.differential K f hf z).comp
    (MukaiEulerFieldPoint.sourceCoordinates K (point K f z) (pointFrame K f z e)).toLinearMap

theorem inputDifferential_surjective : Function.Surjective (inputDifferential K f hf z e) :=
  (MukaiConormalChartDifferential.differential_surjective K f hf z).comp
    (MukaiEulerFieldPoint.sourceCoordinates K (point K f z) (pointFrame K f z e)).surjective

theorem inputDifferential_conormal_zero (y : MukaiConormalFieldCoordinates.Source K (point K f z)) :
    inputDifferential K f hf z e (MukaiEulerFieldPoint.conormalInput K (point K f z) y) = 0 := by
  have h := MukaiEulerFieldPoint.integralDifferential_conormal_zero K (point K f z)
    (pointFrame K f z e) y
  have h₀ : MukaiConormalFieldDifferential.differential K (point K f z)
      (MukaiEulerFieldPoint.sourceCoordinates K (point K f z) (pointFrame K f z e)
        (MukaiEulerFieldPoint.conormalInput K (point K f z) y)) = 0 := by
    change (moduleSpecΓFunctor.map
      ((Scheme.Modules.pullback (point K f z)).map
        (MukaiConormalDifferentialTransport.integralDifferential K))).hom
      ((moduleSpecΓFunctor.map
        ((Scheme.Modules.pullbackComp (point K f z) (integralPrimitivePlucker K)).inv.app
          (Scheme.Hom.relativeDifferentials (MukaiConormalCotangentTransport.integralProjection 13)))).hom
        (MukaiEulerFieldPoint.sourceCoordinates K (point K f z) (pointFrame K f z e)
          (MukaiEulerFieldPoint.conormalInput K (point K f z) y))) = 0 at h
    rw [MukaiConormalFieldDifferential.differential,
      MukaiConormalFieldDifferential.differentialSheaf,
      CategoryTheory.Functor.map_comp]
    exact h
  change (moduleSpecΓFunctor.map (MukaiConormalChartDifferential.pointCotangentIso K f hf z).hom).hom
    (MukaiConormalFieldDifferential.differential K (point K f z)
      (MukaiEulerFieldPoint.sourceCoordinates K (point K f z) (pointFrame K f z e)
        (MukaiEulerFieldPoint.conormalInput K (point K f z) y))) = 0
  rw [h₀, map_zero]

omit [IsAlgClosed K] [Etale f] in
theorem framedCoordinate_eq (j : Fin 14) :
    ProjectiveRatioFieldValues.framedCoordinate (MukaiConormalChartFrame.projectiveMap K f)
      (MukaiConormalChartFrame.positiveFrame K f e) j = tuple K f e j :=
  MukaiConormalChartFrame.positiveFrame_coordinate K f e j

omit [IsAlgClosed K] [Etale f] in
theorem coordinateValue_eq (j : Fin 14) :
    ProjectiveRatioFieldValues.coordinateValue K z (MukaiConormalChartFrame.projectiveMap K f)
      (MukaiConormalChartFrame.positiveFrame K f e) j = value K z (tuple K f e j) := by
  change (Scheme.ΓSpecIso (.of K)).hom
    (z.appTop (ProjectiveRatioFieldValues.framedCoordinate (MukaiConormalChartFrame.projectiveMap K f)
      (MukaiConormalChartFrame.positiveFrame K f e) j)) = _
  rw [framedCoordinate_eq]
  rfl

omit [IsAlgClosed K] in
theorem pointCotangentMap_eq :
    MukaiConormalChartDifferential.differential K f hf z =
      ProjectiveRatioFieldDifferential.pointCotangentMapOfEq K z (chartProjection K)
        (MukaiConormalChartFrame.projectiveMap K f) (projectivePoint K f z)
        (Category.assoc z f (integralPrimitivePlucker K)) := by
  rw [MukaiConormalChartDifferential.differential_eq_direct]
  ext x
  simp only [ProjectiveRatioFieldDifferential.pointCotangentMapOfEq,
    ProjectiveRatioFieldDifferential.pointCotangentMap,
    ProjectiveRatioFieldDifferential.projectiveDifferential,
    MukaiConormalChartDifferential.directDifferentialSheaf,
    CategoryTheory.Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl

omit [IsAlgClosed K] [Etale f] in
theorem pivot_exists : ∃ i : Fin 14, PivotCondition K f z i := by
  have hc : (⨆ i : Fin 14,
      Proj.basicOpen (polyGrading (ULift.{u} ℤ) 13) (MvPolynomial.X i)) = ⊤ :=
    Proj.iSup_basicOpen_eq_top _ _
      (projectiveSpaceOver.irrelevant_coordGrading_le_span_X 13)
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (hc.ge
    (show ProjectiveEulerFieldPoint.image (ULift.{u} ℤ) 13 K (projectivePoint K f z) ∈ ⊤ from trivial))
  exact ⟨i,hi⟩

variable (i : Fin 14) (hp : PivotCondition K f z i)

include hp in
omit [IsAlgClosed K] [Etale f] in
theorem pivot_ne_zero : value K z (tuple K f e i) ≠ 0 := by
  have hp' : ProjectiveEulerFieldPoint.image (ULift.{u} ℤ) 13 K
      (z ≫ MukaiConormalChartFrame.projectiveMap K f) ∈
        ProjectiveSpectrum.basicOpen (polyGrading (ULift.{u} ℤ) 13) (MvPolynomial.X i) := by
    simpa only [MukaiConormalChartFrame.projectiveMap, ← Category.assoc] using hp
  simpa only [coordinateValue_eq] using ProjectiveRatioFieldValues.coordinateValue_ne_zero
    K z (MukaiConormalChartFrame.projectiveMap K f) (MukaiConormalChartFrame.positiveFrame K f e) i hp'

theorem ratio_values (j : Fin 14) :
    value K z (tuple K f e j) = pointRatio K f z i hp j * value K z (tuple K f e i) := by
  have h := ProjectiveRatioFieldValues.ratio_eq_coordinateValue_div_of_eq K z
    (MukaiConormalChartFrame.projectiveMap K f) (MukaiConormalChartFrame.positiveFrame K f e)
    i (projectivePoint K f z) (Category.assoc z f (integralPrimitivePlucker K)) hp j
  rw [coordinateValue_eq, coordinateValue_eq] at h
  rw [show pointRatio K f z i hp j = value K z (tuple K f e j) / value K z (tuple K f e i) from h]
  exact (div_mul_cancel₀ _ (pivot_ne_zero K f z e i hp)).symm

theorem ratio_derivatives (j : {j : Fin 14 // j ≠ i}) :
    derivative K z (tuple K f e j.1) - pointRatio K f z i hp j.1 • derivative K z (tuple K f e i) =
      value K z (tuple K f e i) • inputDifferential K f hf z e (pointBasis K f z e i hp j) := by
  have hd := ProjectiveRatioFieldDifferential.pointCotangentMapOfEq_basis K z (chartProjection K)
    (MukaiConormalChartFrame.projectiveMap K f) (MukaiConormalChartFrame.positiveFrame K f e) i
    (projectivePoint K f z) (Category.assoc z f (integralPrimitivePlucker K)) hp j
  have hb : inputDifferential K f hf z e (pointBasis K f z e i hp j) =
      (value K z (tuple K f e i) ^ 2)⁻¹ •
        (value K z (tuple K f e i) • derivative K z (tuple K f e j.1) -
          value K z (tuple K f e j.1) • derivative K z (tuple K f e i)) := by
    change MukaiConormalChartDifferential.differential K f hf z
      (MukaiEulerFieldPoint.sourceCoordinates K (point K f z) (pointFrame K f z e)
        (MukaiEulerFieldPoint.basis K (point K f z) (pointFrame K f z e) i hp j)) = _
    rw [MukaiConormalCoefficientImage.sourceCoordinates_basis, pointCotangentMap_eq]
    simpa only [coordinateValue_eq, ProjectiveRatioFieldDifferential.pointDerivative,
      framedCoordinate_eq, derivative] using hd
  have hr : pointRatio K f z i hp j.1 =
      value K z (tuple K f e j.1) / value K z (tuple K f e i) := by
    exact (eq_div_iff (pivot_ne_zero K f z e i hp)).mpr (ratio_values K f z e i hp j.1).symm
  have hi := pivot_ne_zero K f z e i hp
  have h₁ : value K z (tuple K f e i) *
      ((value K z (tuple K f e i) ^ 2)⁻¹ * value K z (tuple K f e i)) = 1 := by
    field_simp [hi]
  have h₂ : value K z (tuple K f e i) *
      ((value K z (tuple K f e i) ^ 2)⁻¹ * value K z (tuple K f e j.1)) =
        value K z (tuple K f e j.1) / value K z (tuple K f e i) := by
    field_simp [hi]
  rw [hb, hr]
  simp only [smul_sub, smul_smul, h₁, h₂, one_smul]

end M9Native.MukaiConormalChartRatioData
