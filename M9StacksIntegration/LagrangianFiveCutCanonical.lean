module

public import M9StacksIntegration.LagrangianFibreAdjunction
public import M9StacksIntegration.LagrangianBertiniPoint
public import M9StacksIntegration.LagrangianFiveCutDegree
public import M9StacksIntegration.SmoothConnectedCurve
public import M9StacksIntegration.SmoothCurveCanonicalDifferentials
public import M9StacksIntegration.UniversalLagrangianNativeGenus

/-!
# The actual original five-cut canonical line and genus-degree relation

The actual same-field zero-scheme model is constructed from the original
parameter and composed with the original Bertini fibre isomorphism.
Both the original LG immersion and Spec K projection are retained.
The already-proved adjunction and native differential comparison then
identify the original differential/canonical line. Actual Cartier
degree descent yields 2g-2 equal to the actual sixfold LG degree.

No model, curve class, smoothness, line comparison, genus or degree16
premise is supplied. The numerical LG degree remains separate.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace M9Native.LagrangianFiveCutCanonical
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LagrangianLinearSections
open SmoothIntegralHyperplaneCuts LagrangianBertiniPoint
open Stacks.Duality (dualizingSheafOverField)

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]

abbrev structureMap : fiveCutCurve K ⟶ Spec (.of K) :=
  fiveCutToLG K ≫ LagrangianGrassmannian.projection K

abbrev curveLine : (fiveCutCurve K).Modules :=
  (Scheme.Modules.pullback (fiveCutToLG K)).obj (LagrangianPluckerQuotient.determinantLine K)

local instance structureMap_smooth : Smooth (structureMap K) := by
  change Smooth (fiveCutToLG K ≫ LagrangianGrassmannian.projection K)
  rw [← initialSystem_toBase K]
  exact fiveCutCurve_smooth K

local instance structureMap_isCurve : IsCurve K (structureMap K) := by
  let : ConnectedSpace (fiveCutCurve K) := fiveCutCurve_connected K
  exact SmoothConnectedCurve.isCurve_of_smooth_connected (structureMap K)
    (fiveCutCurve_dimension K)

/-- The original five-cut differential line is the original determinant
restriction. The actual model and both of its original maps are derived. -/
def differentialsIsoCurveLine :
    Scheme.Hom.relativeDifferentials (structureMap K) ≅ curveLine K := by
  let := smoothOfRelativeDimension_one_of_isCurve K (structureMap K)
  let hModel := LagrangianFibreFiveSection.every_parameter_fiveSection K
    (parameterPoint K) (parameterPoint_projection K)
  let s : Γ(LagrangianFiveSectionModel.equationBundle K, ⊤) := Classical.choose hModel
  let e₀ : LagrangianFiveSectionModel.curve K s ≅
      LagrangianFibreFactorization.fibre K (parameterPoint K) :=
    Classical.choose (Classical.choose_spec hModel)
  have he₀ : e₀.hom ≫ LagrangianFibreFactorization.fibreToLG K (parameterPoint K) =
      LagrangianFiveSectionModel.inclusion K s :=
    Classical.choose_spec (Classical.choose_spec hModel)
  let eF : LagrangianFiveSectionModel.curve K s ≅
      pullback (familyProjection K) (parameterPoint K) :=
    e₀ ≪≫ pullbackSymmetry (parameterPoint K) (familyProjection K)
  have heF : eF.hom ≫ pullback.fst (familyProjection K) (parameterPoint K) ≫
      familyToLG K = LagrangianFiveSectionModel.inclusion K s := by
    simpa only [eF, Iso.trans_hom, Category.assoc,
      pullbackSymmetry_hom_comp_fst_assoc, LagrangianFibreFactorization.fibreToLG] using he₀
  let e : fiveCutCurve K ≅ LagrangianFiveSectionModel.curve K s :=
    cutIsoPointFibre K ≪≫ eF.symm
  have heLG : e.hom ≫ LagrangianFiveSectionModel.inclusion K s = fiveCutToLG K := by
    rw [← heF]
    simpa only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc] using
      cutIsoPointFibre_hom_toLG K
  have heBase : e.hom ≫ LagrangianFiveSectionModel.structureMap K s = structureMap K := by
    change e.hom ≫ (LagrangianFiveSectionModel.inclusion K s ≫
      LagrangianGrassmannian.projection K) = fiveCutToLG K ≫ LagrangianGrassmannian.projection K
    rw [← Category.assoc, heLG]
  exact LagrangianFibreAdjunction.differentialsIsoOfModel K (structureMap K) s e heBase ≪≫
    (Scheme.Modules.pullbackCongr heLG).app (LagrangianPluckerQuotient.determinantLine K)

/-- The native original dualizing sheaf has the same actual determinant
restriction, using the separately proved native omega/Omega comparison. -/
def canonicalIsoCurveLine : dualizingSheafOverField (structureMap K) ≅ curveLine K :=
  SmoothCurveCanonicalDifferentials.canonicalDifferentialsIso (structureMap K) ≪≫
    differentialsIsoCurveLine K

/-- The actual native genus of the original five-cut curve satisfies
2g-2 equal to the original LG sixfold ample degree, with no numerical
degree hypothesis. -/
theorem genus_degree_relation :
    2 * (genus (structureMap K) : ℤ) - 2 =
      degreeWithRespectTo K (LagrangianGrassmannian.projection K)
        (𝟙 (LagrangianGrassmannian.space K)) 6 (LagrangianIntegral.space_dimension K)
        (LagrangianPluckerQuotient.determinantLine K)
        (LagrangianDegree.determinantLine_modulesIsAmple K) := by
  let := SmoothCurveCanonicalDifferentials.differentials_isInvertible (structureMap K)
  let : SheafOfModules.IsInvertible (fiveCutCurve K).presheaf
      (fiveCutCurve K).ringCatSheaf.2 (curveLine K) :=
    Stacks.SheafOfModules.isInvertible_of_iso _ _ (differentialsIsoCurveLine K)
  have hOmega := SmoothCurveCanonicalDifferentials.differentials_degree_of_isAlgClosed
    (structureMap K) (fiveCutCurve_dimension K).le
  have hIso := invertibleCurveDegree_eq_of_iso K (structureMap K)
    (fiveCutCurve_dimension K).le (differentialsIsoCurveLine K)
  exact hOmega.symm.trans (hIso.trans (LagrangianFiveCutDegree.fiveCut_curveDegree K))

/-- The same genuine relation for the actual computed genus of the
original universal good-open family, whose native classifier is fixed. -/
theorem family_genus_degree_relation :
    2 * (UniversalLagrangianNativeGenus.fibreGenus K : ℤ) - 2 =
      degreeWithRespectTo K (LagrangianGrassmannian.projection K)
        (𝟙 (LagrangianGrassmannian.space K)) 6 (LagrangianIntegral.space_dimension K)
        (LagrangianPluckerQuotient.determinantLine K)
        (LagrangianDegree.determinantLine_modulesIsAmple K) := by
  rw [UniversalLagrangianNativeGenus.fibreGenus_eq_fiveCut_genus K]
  exact genus_degree_relation K

end M9Native.LagrangianFiveCutCanonical
