module

public import M9StacksIntegration.LagrangianBetaFourCut
public import M9StacksIntegration.CurveSectionZeroChowDegree
public import M9StacksIntegration.LagrangianTransverseGoodOpen
public import M9StacksIntegration.SchemeGlobalSectionsIso

/-!
# The actual beta divisor degree and the canonical residual degree

The beta line and section are the determinant line and selected original
pair section of the genuine rank-two image. Its full native zero scheme
has line degree equal to its actual global-function dimension. The proved
four-cut isomorphism transports this dimension with the original field
action. The actual beta/alpha/canonical tensor isomorphism then computes
the residual degree. No numerical intersection value is supplied here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open Stacks.Chow

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

universe u

namespace M9Native.LagrangianBetaCurveDegree

open M9Native.SchemeGlobalSectionsIso


open LagrangianOrderedFibre LagrangianRankTwoSubsystemBundles
open LagrangianRankTwoSubsystemExistence LagrangianBetaRankDrop LagrangianBetaFourCut
open M9Native.MukaiBundleDeterminant

variable (K : Type u) [Field K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  [IsIntegral (model K M hM)]
  [SmoothOfRelativeDimension 1 (modelProjection K M hM)]

theorem model_dimension_le_one : topologicalKrullDim (model K M hM) ≤ 1 := by
  let := model_isCurve K M hM
  exact (IsCurve.topologicalKrullDim_eq_one (modelProjection K M hM)).le

def betaDegree (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) : ℤ := by
  letI := beta_isInvertible K M hM s hr
  exact invertibleCurveDegree K (modelProjection K M hM) (model_dimension_le_one K M hM)
    (beta K M hM s)

def alphaDegree (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) : ℤ := by
  letI := alpha_isInvertible K M hM s hr
  exact invertibleCurveDegree K (modelProjection K M hM) (model_dimension_le_one K M hM)
    (alpha K M hM s)

/-- The literal native Chow zero ideal of the actual original beta section. -/
abbrev nativeBetaZeroIdeal (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) (e : Fin 2 ↪ Fin 3) :=
  Stacks.Chow.zeroSchemeOfSection (model K M hM) (beta K M hM s) (betaSection K M hM s hr e)

abbrev nativeBetaZeroProjection (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) (e : Fin 2 ↪ Fin 3) :=
  (nativeBetaZeroIdeal K M hM s hr e).subschemeι ≫ modelProjection K M hM

def nativeBetaZeroLength (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) (e : Fin 2 ↪ Fin 3) : ℕ := by
  letI : Algebra K Γ((nativeBetaZeroIdeal K M hM s hr e).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (nativeBetaZeroProjection K M hM s hr e).appTop).hom.toAlgebra
  exact finrank K Γ((nativeBetaZeroIdeal K M hM s hr e).subscheme, ⊤)

theorem nativeBetaZero_finite (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) (e : Fin 2 ↪ Fin 3)
    (hs : betaSection K M hM s hr e ≠ 0) :
    IsFinite (nativeBetaZeroProjection K M hM s hr e) := by
  let := beta_isInvertible K M hM s hr
  exact CurveSectionZeroChowDegree.zero_finite (beta K M hM s) (betaSection K M hM s hr e)
    K (modelProjection K M hM) (model_dimension_le_one K M hM) hs

/-- Actual line degree equals the dimension of functions on the SAME
full native zero scheme, without a finite/length/degree hypothesis. -/
theorem betaDegree_eq_nativeBetaZeroLength (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) (e : Fin 2 ↪ Fin 3)
    (hs : betaSection K M hM s hr e ≠ 0) :
    betaDegree K M hM s hr = (nativeBetaZeroLength K M hM s hr e : ℤ) := by
  let := beta_isInvertible K M hM s hr
  exact invertibleCurveDegree_eq_finrank_globalSections_zeroScheme_of_dim_le_one
    K (modelProjection K M hM) (model_dimension_le_one K M hM) (beta K M hM s)
    (CurveSectionZeroChowDegree.nativeSection (beta K M hM s) (betaSection K M hM s hr e))
    (by simpa only [CurveSectionZeroChowDegree.nativeSection_eval] using hs)
    (nativeBetaZeroIdeal K M hM s hr e)
    (CurveSectionZeroChowDegree.nativeSection_zero_geometric
      (beta K M hM s) (betaSection K M hM s hr e))

theorem betaChowDegree_eq_betaDegree (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) (e : Fin 2 ↪ Fin 3)
    (hs : betaSection K M hM s hr e ≠ 0) :
    chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (modelProjection K M hM) (IsLocalRing.closedPoint K)
      (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation K)
        (modelProjection K M hM) (nativeBetaZeroIdeal K M hM s hr e).subschemeι 0)) =
      betaDegree K M hM s hr := by
  let := beta_isInvertible K M hM s hr
  exact CurveSectionZeroChowDegree.chowDegree_zero_eq_invertibleCurveDegree
    (beta K M hM s) (betaSection K M hM s hr e) K (modelProjection K M hM)
    (model_dimension_le_one K M hM) hs

abbrev fourCutProjection (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3)
    (A : Matrix.GeneralLinearGroup (Fin 5) K) :=
  (fourIdeal K s e (A.val * M)).subschemeι ≫
    rankDropInclusion K s e ≫ LagrangianGrassmannian.projection K

def fourCutLength (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3)
    (A : Matrix.GeneralLinearGroup (Fin 5) K) : ℕ := by
  letI : Algebra K Γ((fourIdeal K s e (A.val * M)).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (fourCutProjection K M s e A).appTop).hom.toAlgebra
  exact finrank K Γ((fourIdeal K s e (A.val * M)).subscheme, ⊤)

theorem nativeBetaZeroIsoFourCut_over (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) (e : Fin 2 ↪ Fin 3)
    (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    (nativeBetaZeroIsoFourCut K M hM s hr e A hfirst).hom ≫ fourCutProjection K M s e A =
      nativeBetaZeroProjection K M hM s hr e := by
  simpa only [fourCutProjection, nativeBetaZeroProjection, modelProjection, Category.assoc] using
    congrArg (fun a => a ≫ LagrangianGrassmannian.projection K)
      (nativeBetaZeroIsoFourCut_hom_toLG K M hM s hr e A hfirst)

/-- The dimension is transported by the genuine original-field scheme
isomorphism, not by a replacement field or a reduced support. -/
theorem nativeBetaZeroLength_eq_fourCutLength (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) (e : Fin 2 ↪ Fin 3)
    (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    nativeBetaZeroLength K M hM s hr e = fourCutLength K M s e A :=
  finrank_globalSections_eq K (nativeBetaZeroProjection K M hM s hr e)
    (fourCutProjection K M s e A) (nativeBetaZeroIsoFourCut K M hM s hr e A hfirst)
    (nativeBetaZeroIsoFourCut_over K M hM s hr e A hfirst)

theorem betaDegree_eq_fourCutLength (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) (e : Fin 2 ↪ Fin 3)
    (hs : betaSection K M hM s hr e ≠ 0) (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    betaDegree K M hM s hr = (fourCutLength K M s e A : ℤ) :=
  (betaDegree_eq_nativeBetaZeroLength K M hM s hr e hs).trans
    (congrArg Int.ofNat (nativeBetaZeroLength_eq_fourCutLength K M hM s hr e A hfirst))

section CanonicalResidual

variable [IsAlgClosed K]

theorem betaDegree_add_alphaDegree_eq_genus (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) :
    betaDegree K M hM s hr + alphaDegree K M hM s hr =
      2 * (genus (modelProjection K M hM) : ℤ) - 2 := by
  let := model_isCurve K M hM
  let : Smooth (modelProjection K M hM) := SmoothOfRelativeDimension.smooth 1 _
  let := beta_isInvertible K M hM s hr
  let := alpha_isInvertible K M hM s hr
  let := CurveCanonicalInvertibility.dualizing_isInvertible (modelProjection K M hM)
  let ec := betaTensorAlphaCanonicalIso K M hM s hr
  let : SheafOfModules.IsInvertible (model K M hM).presheaf (model K M hM).ringCatSheaf.property
      (tensor (beta K M hM s) (alpha K M hM s)) :=
    Stacks.SheafOfModules.isInvertible_of_iso _ _ ec.symm
  let := isIso_globalSections_of_isAlgClosed K (modelProjection K M hM)
  exact (invertibleCurveDegree_tensorSheaf_eq_add K (modelProjection K M hM)
    (model_dimension_le_one K M hM) (beta K M hM s) (alpha K M hM s)).symm.trans
      ((invertibleCurveDegree_eq_of_iso K (modelProjection K M hM)
        (model_dimension_le_one K M hM) ec).trans
          (CanonicalLineCohomology.canonical_degree
            (modelProjection K M hM) (model_dimension_le_one K M hM)))

theorem alphaDegree_eq_genus_sub_fourCutLength (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) (e : Fin 2 ↪ Fin 3)
    (hs : betaSection K M hM s hr e ≠ 0) (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    alphaDegree K M hM s hr =
      2 * (genus (modelProjection K M hM) : ℤ) - 2 - (fourCutLength K M s e A : ℤ) := by
  have hsum := betaDegree_add_alphaDegree_eq_genus K M hM s hr
  have hb := betaDegree_eq_fourCutLength K M hM s hr e hs A hfirst
  omega

omit [IsAlgClosed K] [IsIntegral (model K M hM)]
  [SmoothOfRelativeDimension 1 (modelProjection K M hM)] in
theorem model_genus_eq_ordered :
    genus (modelProjection K M hM) = genus (LagrangianTransverseRestriction.curveProjection K M) := by
  let ep := cutIsoModel K M hM
  have hb : ep.inv ≫ LagrangianTransverseRestriction.curveProjection K M =
      modelProjection K M hM :=
    ep.inv_comp_eq.mpr (cutIsoModel_hom_base K M hM).symm
  apply genus_baseChange K K ep.inv (modelProjection K M hM)
    (LagrangianTransverseRestriction.curveProjection K M)
  rw [show Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (.of K)) by simp]
  exact IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using hb⟩

/-- The actual sixfold ample degree of the ORIGINAL native LG and its
ORIGINAL determinant line, before its numerical evaluation. -/
abbrev lagrangianDegree : ℤ :=
  degreeWithRespectTo K (LagrangianGrassmannian.projection K)
    (𝟙 (LagrangianGrassmannian.space K)) 6 (LagrangianIntegral.space_dimension K)
    (LagrangianPluckerQuotient.determinantLine K)
    (LagrangianDegree.determinantLine_modulesIsAmple K)

theorem model_genus_degree_relation :
    2 * (genus (modelProjection K M hM) : ℤ) - 2 = lagrangianDegree K := by
  let := LagrangianModelRestriction.ordered_integral K M hM
  let := LagrangianModelRestriction.ordered_smooth K M hM
  rw [model_genus_eq_ordered K M hM]
  exact LagrangianTransverseGoodOpen.genus_degree_relation K M hM

theorem betaDegree_add_alphaDegree_eq_lagrangianDegree (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) :
    betaDegree K M hM s hr + alphaDegree K M hM s hr = lagrangianDegree K :=
  (betaDegree_add_alphaDegree_eq_genus K M hM s hr).trans (model_genus_degree_relation K M hM)

theorem alphaDegree_eq_lagrangianDegree_sub_fourCutLength (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) (e : Fin 2 ↪ Fin 3)
    (hs : betaSection K M hM s hr e ≠ 0) (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    alphaDegree K M hM s hr = lagrangianDegree K - (fourCutLength K M s e A : ℤ) := by
  have hsum := betaDegree_add_alphaDegree_eq_lagrangianDegree K M hM s hr
  have hb := betaDegree_eq_fourCutLength K M hM s hr e hs A hfirst
  omega

/-- The original smooth integral model supplies all selected sections,
the genuine equation change and the degree identities. No beta section,
nonzero relation, field identification, length or numerical class is input. -/
theorem exists_actual_pair_degrees :
    ∃ (s : Fin 3 → (Fin 6 → K))
      (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
      (e : Fin 2 ↪ Fin 3) (A : Matrix.GeneralLinearGroup (Fin 5) K),
      LinearIndependent K s ∧ LinearIndependent K (s ∘ e) ∧
      betaSection K M hM s hr e ≠ 0 ∧
      (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s ∧
      IsFinite (fourCutProjection K M s e A) ∧
      betaDegree K M hM s hr = (fourCutLength K M s e A : ℤ) ∧
      alphaDegree K M hM s hr = lagrangianDegree K - (fourCutLength K M s e A : ℤ) := by
  obtain ⟨s, hr, e, A, hs, hpair, hβ, _hAM, hfirst, _hdet, _hiso, hfinite⟩ :=
    LagrangianBetaFourCut.exists_finite_fourCut K M hM
  exact ⟨s, hr, e, A, hs, hpair, hβ, hfirst, hfinite,
    betaDegree_eq_fourCutLength K M hM s hr e hβ A hfirst,
    alphaDegree_eq_lagrangianDegree_sub_fourCutLength K M hM s hr e hβ A hfirst⟩

end CanonicalResidual

end M9Native.LagrangianBetaCurveDegree

end
