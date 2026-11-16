module

public import M9StacksIntegration.LagrangianOriginalSixBasis
public import M9StacksIntegration.MukaiCanonicalBundleCurveIso
public import M9StacksIntegration.MukaiSymplecticBasisChange
public import M9StacksIntegration.MukaiEvaluationMatrix
public import M9StacksIntegration.LagrangianIsotropicRestriction
public import M9StacksIntegration.LagrangianPluckerTrivialization

/-!
# Actual curve isomorphisms give native LG symmetries

The canonical generated semi-irreducible properties and the actual
nonpentagonal genus-nine source curve supply the bundle isomorphism by
the proved net-free uniqueness theorem. The original six quotient
sections form complete bases by the actual restriction-rank theorem.
The symplectic matrix is derived from those bases and the actual
exterior-evaluation kernel. Its scalar correction is retained in a
genuine quotient-presentation isomorphism, so the native LG classifier
gives an equality of the original scheme morphisms.

There is no supplied bundle isomorphism, H0 comparison, polarization,
LG-action equality, or parameter-orbit premise. The canonical bundle
properties and true genus/nonpentagonality remain honest intermediate
geometric hypotheses; this does not establish a reverse quotient factory.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Matrix
open scoped BigOperators Matrix
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

universe u
namespace M9Native.MukaiCurveIsoLagrangianAction

open AlgebraicGeometry.Grassmannian LagrangianPluckerQuotient
open LagrangianTransverseRestriction LagrangianUniversalSections
open MukaiCanonicalBundleFromNet MukaiLagrangianMap MukaiEvaluationChoices

/-- The actual universal quotient on LG gives the literal native
Grassmannian class, with the actual composite pullback comparison. -/
theorem quotientClass_eq_pointClass (K : Type u) [Field K]
    {T : Scheme.{u}} (l : T ⟶ LagrangianGrassmannian.space K) :
    (⟦quotient K l⟧ : Points T 3 6) = LagrangianSymplecticAction.pointClass K l := by
  obtain ⟨e, he⟩ := LagrangianPluckerTrivialization.pullbackPresentation_comp_isomorphic
    (LagrangianGrassmannian.inclusion K) l (LagrangianGrassmannian.universalQuotient K)
  exact Quotient.sound (.rel _ _ ⟨e, he⟩)

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (M N : Matrix (Fin 5) (Fin 14) K)
  [IsIntegral (curve K M)] [SmoothOfRelativeDimension 1 (curveProjection K M)]
  [IsIntegral (curve K N)] [SmoothOfRelativeDimension 1 (curveProjection K N)]

local instance sourceSmooth : Smooth (curveProjection K M) :=
  SmoothOfRelativeDimension.smooth 1 _
local instance targetSmooth : Smooth (curveProjection K N) :=
  SmoothOfRelativeDimension.smooth 1 _

set_option maxHeartbeats 2400000 in
/-- A genuine original over-field curve isomorphism determines an
actual native symplectic LG action. The required quotient-bundle
isomorphism is constructed from the actual canonical properties. -/
theorem exists_lagrangian_action_of_curveIso
    (hM : Function.Surjective M.mulVec) (hN : Function.Surjective N.mulVec)
    (e : curve K M ≅ curve K N)
    (he : e.hom ≫ curveProjection K N = curveProjection K M)
    (hg : genus (curveProjection K M) = 9)
    (hnp : ¬ Nonempty (LinearSeries K (curveProjection K M)
      (IsCurve.topologicalKrullDim_eq_one (k := K) (f := curveProjection K M)).le 5 1))
    (hQC : IsCanonicalGeneratedSemi (curveProjection K M) (bundle K (inclusion K M)))
    (hQD : IsCanonicalGeneratedSemi (curveProjection K N) (bundle K (inclusion K N))) :
    ∃ g : Matrix.symplecticGroup (Fin 3) K,
      inclusion K M = e.hom ≫ inclusion K N ≫ LagrangianSymplecticAction.action K g := by
  let EC := bundle K (inclusion K M)
  let ED := bundle K (inclusion K N)
  let EP := (Scheme.Modules.pullback e.hom).obj ED
  let qC := quotient K (inclusion K M)
  let qD := quotient K (inclusion K N)
  let qP := pullbackPresentation e.hom qD
  obtain ⟨hQP, ⟨a⟩⟩ := MukaiCanonicalBundleCurveIso.canonical_properties_on_two_curves
    K (curveProjection K M) (curveProjection K N) e he hg hnp EC ED hQC hQD
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} EP 3 := hQP.1
  let bC := LagrangianOriginalSixBasis.originalBasis K M hM hQC
  let bD := LagrangianOriginalSixBasis.originalBasis K N hN hQD
  let bP := bD.map (MukaiCurveIsoPullback.h0PullbackEquiv
    K (curveProjection K M) (curveProjection K N) e he ED)
  have hEC : MukaiSemiIrreducible.evaluation K (curveProjection K M) EC bC = qC.map :=
    LagrangianOriginalSixBasis.evaluation_originalBasis K M hM hQC
  have hED : MukaiSemiIrreducible.evaluation K (curveProjection K N) ED bD = qD.map :=
    LagrangianOriginalSixBasis.evaluation_originalBasis K N hN hQD
  have hEP : MukaiSemiIrreducible.evaluation K (curveProjection K M) EP bP = qP.map := by
    have h := MukaiCurveIsoPullback.evaluation_pullback K (curveProjection K M)
      (curveProjection K N) e he ED bD
    rw [hED] at h
    exact h.symm
  have hσC : ExteriorEvaluation.lambda K (curveProjection K M) EC 2
      (basisSigma K (curveProjection K M) EC bC) = 0 :=
    LagrangianOriginalSixBasis.basisSigma_lambda_eq_zero K M hM hQC
  have hσP : ExteriorEvaluation.lambda K (curveProjection K M) EP 2
      (basisSigma K (curveProjection K M) EP bP) = 0 := by
    apply (evaluation_annihilatesSigma_iff K (curveProjection K M) EP bP).mp
    rw [hEP]
    exact LagrangianIsotropicRestriction.pulledQuotient_annihilates e.hom qD.map
      (LagrangianUniversalSectionInjection.universal_quotient_annihilates K (inclusion K N))
  obtain ⟨cP⟩ := hQP.2.2.1
  obtain ⟨t, g, ht, hG⟩ := MukaiSymplecticBasisChange.exists_symplectic_coordinate_change
    K (curveProjection K M) a bC bP cP hg hQP.2.2.2.2 hσC hσP
  let a' : EC ≅ EP := a ≪≫ MukaiEvaluationMatrix.scalarIso K (curveProjection K M) EP t ht
  have htriangle : qC.map ≫ a'.hom =
      (LagrangianSymplecticAction.constantFreeIso K (curveProjection K M) g).hom ≫ qP.map := by
    rw [← hEC, ← hEP, MukaiEvaluationMatrix.constantFreeIso_eq_constantMap, hG,
      MukaiEvaluationMatrix.evaluation_precomp_matrix K (curveProjection K M) EP bP
        (t • MukaiSymplecticBasisChange.coordinateMatrix K (curveProjection K M) a bC bP)]
    rw [show a'.hom = a.hom ≫ (MukaiEvaluationMatrix.scalarIso K (curveProjection K M) EP t ht).hom
      from rfl, ← Category.assoc, MukaiEvaluationChoices.evaluation_postcomp,
      MukaiEvaluationMatrix.evaluation_scalarIso]
    congr 1
    funext j
    change t • h0Equiv K (curveProjection K M) a (bC j) =
      bP.equivFun.symm (t • (MukaiSymplecticBasisChange.coordinateMatrix
        K (curveProjection K M) a bC bP).col j)
    rw [map_smul, MukaiSymplecticBasisChange.coordinateMatrix_column,
      LinearEquiv.symm_apply_apply]
  have hquot : qC.Isomorphic
      (LagrangianSymplecticAction.transform K (curveProjection K M) g qP) := ⟨a', htriangle⟩
  have hb : (e.hom ≫ inclusion K N) ≫ LagrangianGrassmannian.projection K = curveProjection K M := by
    simpa only [Category.assoc] using he
  have hclassP : (⟦qP⟧ : Points (curve K M) 3 6) =
      LagrangianSymplecticAction.pointClass K (e.hom ≫ inclusion K N) := by
    change pullbackPointsMap e.hom 3 6 (⟦qD⟧ : Points (curve K N) 3 6) = _
    rw [quotientClass_eq_pointClass K (inclusion K N),
      ← LagrangianSymplecticAction.pointClass_comp]
  refine ⟨g, ?_⟩
  apply LagrangianSymplecticAction.hom_ext K
  · simp only [Category.assoc, LagrangianSymplecticAction.action_projection]
    exact he.symm
  · rw [← quotientClass_eq_pointClass K (inclusion K M),
      ← Category.assoc,
      LagrangianSymplecticAction.pointClass_action, hb]
    change (⟦qC⟧ : Points (curve K M) 3 6) =
      LagrangianSymplecticAction.transformPoints K (curveProjection K M) g _
    rw [← hclassP]
    exact Quotient.sound (.rel _ _ hquot)

end M9Native.MukaiCurveIsoLagrangianAction
