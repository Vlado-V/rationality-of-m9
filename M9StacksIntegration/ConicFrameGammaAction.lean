module

public import M9StacksIntegration.ConicFrameNativeGeometry
public import M9StacksIntegration.NativeFunctionFieldFunctor
public import M9.FrameProjectiveRatios
import all M9.Private.ProjectiveCharts

/-! The actual right tetrahedral action on native projective matrix space,
transported through the genuine pinned isomorphism of its two Proj models. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite

namespace M9Native.ConicFrameGammaAction

abbrev Gamma := M9.TetrahedralGroup.Gamma
abbrev projectiveSpace := ConicFrameProjective.space ℂ
abbrev projectiveField := projectiveSpace.functionField

/-- The right frame factor, inside the already proved concrete frame group. -/
def rightEmbedding : Gamma →* M9.FrameAction.TetrahedralFrameGroup where
  toFun g := ⟨g,1,false⟩
  map_one' := rfl
  map_mul' g h := by
    simp [M9.FrameAction.FrameGroup.mul_even]

theorem rightEmbedding_injective : Function.Injective rightEmbedding := by
  intro g h heq
  exact congrArg M9.FrameAction.FrameGroup.first heq

/-- This is the actual scheme isomorphism supplied by the pinned Proj
base-change comparison, not an identification of rational fields. -/
def nativeSchemeIso : projectiveSpace ≅ M9.ProjectiveFunctionField.matrixSpace :=
  (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison ℂ 8).iso

theorem zeroConstants_eq :
    (M9.ProjectiveGeometry.ProjectiveSpace.degreeZeroConstants 8).toRingHom =
      (GradedRing.projZeroRingHom'
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ℂ 8)).comp
        (algebraMap ℂ (MvPolynomial (Fin 9) ℂ)) := by
  apply RingHom.ext
  intro c
  exact (GradedRing.projZeroRingHom'_apply_coe _
    (M9.ProjectiveGeometry.ProjectiveSpace.degreeZeroConstants 8 c)).symm

theorem nativeSchemeIso_over : nativeSchemeIso.hom ≫ M9.ProjectiveFunctionField.projection 8 =
    ConicFrameProjective.projection ℂ := by
  change nativeSchemeIso.hom ≫
    (Proj.toSpecZero (M9.ProjectiveGeometry.ProjectiveSpace.projectiveGrading 8) ≫
      Spec.map (CommRingCat.ofHom
        (M9.ProjectiveGeometry.ProjectiveSpace.degreeZeroConstants 8).toRingHom)) = _
  rw [zeroConstants_eq,← Category.assoc]
  exact (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison ℂ 8).toBase

/-- The actual generic-stalk pullback of the scheme isomorphism. -/
def nativeFieldEquiv : M9.ProjectiveFunctionField.matrixFunctionField ≃ₐ[ℂ] projectiveField where
  __ := (GrassmannianCharts.openImmersionFunctionFieldIso nativeSchemeIso.hom).commRingCatIsoToRingEquiv
  commutes' c := by
    have h := GrassmannianCharts.openImmersionFunctionFieldIso_scalar ℂ nativeSchemeIso.hom
      (M9.ProjectiveFunctionField.projection 8)
    rw [nativeSchemeIso_over] at h
    exact DFunLike.congr_fun h c

def schemeRepresentation : Gamma →* Aut projectiveSpace :=
  (Aut.autMulEquivOfIso nativeSchemeIso.symm).toMonoidHom.comp
    (M9.FrameProjectiveGeometry.schemeRepresentation.comp rightEmbedding)

theorem schemeRepresentation_hom (g : Gamma) :
    (schemeRepresentation g).asIso.hom = nativeSchemeIso.hom ≫
      (M9.FrameProjectiveGeometry.schemeRepresentation (rightEmbedding g)).asIso.hom ≫
        nativeSchemeIso.inv := rfl

/-- Conjugation by a genuine scheme-induced field isomorphism transports
exactly the frozen native field action. -/
def fieldRepresentation : Gamma →* (projectiveField ≃ₐ[ℂ] projectiveField) where
  toFun g := nativeFieldEquiv.symm.trans
    ((M9.FrameProjectiveGeometry.fieldRepresentation (rightEmbedding g)).trans nativeFieldEquiv)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

theorem fieldRepresentation_apply (g : Gamma) (x : projectiveField) :
    fieldRepresentation g x = nativeFieldEquiv
      (M9.FrameProjectiveGeometry.fieldRepresentation (rightEmbedding g) (nativeFieldEquiv.symm x)) := rfl

theorem schemeRepresentation_injective : Function.Injective schemeRepresentation :=
  (Aut.autMulEquivOfIso nativeSchemeIso.symm).injective.comp
    (M9.FrameProjectiveGeometry.schemeRepresentation_injective.comp rightEmbedding_injective)

theorem fieldRepresentation_injective : Function.Injective fieldRepresentation := by
  intro g h hgh
  apply rightEmbedding_injective
  apply M9.FrameProjectiveGeometry.fieldRepresentation_injective
  ext x
  have hh := congrArg (fun σ : projectiveField ≃ₐ[ℂ] projectiveField =>
    nativeFieldEquiv.symm (σ (nativeFieldEquiv x))) hgh
  simpa only [fieldRepresentation_apply,AlgEquiv.symm_apply_apply] using hh

@[instance_reducible] def fieldAction : MulSemiringAction Gamma projectiveField :=
  MulSemiringAction.compHom projectiveField fieldRepresentation

end M9Native.ConicFrameGammaAction
