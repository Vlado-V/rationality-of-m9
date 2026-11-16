module

public import M9StacksIntegration.LagrangianNonpentagonalQuotientFactory
public import M9StacksIntegration.MukaiCurveIsoLinearSeries
public import M9StacksIntegration.MukaiCanonicalBundleIsoTransport
public import M9StacksIntegration.MukaiCanonicalModuleIsoTransport
public import M9StacksIntegration.LagrangianSectionZeroBoundApplications
public import M9StacksIntegration.LagrangianTransverseGoodOpen

/-!
# Actual ordered and original-fibre applications of the nonpentagonal factory

The full native no-degree-five condition and genus are transported by
an actual curve isomorphism over the original field. Pullback of the
actual universal quotient is identified by its original quotient
triangle; the proved canonical bundle properties therefore transfer to
the literal original quotient. No isomorphism, scalar compatibility,
complete-system property or residual degree is supplied in the actual
ordered/matrix/original-parameter clients.

These results are conditional on the actual curve being genus nine
and nonpentagonal. They do not assert either condition for every good
linear section. Arbitrary native dimension proofs are retained in the
pencil obstruction, which allows basepoints.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
universe u

namespace M9Native.LagrangianQuotientFactoryApplications

open LagrangianUniversalSections LagrangianGrassmannian

private theorem inverse_triangle {X Y Z : Scheme.{u}} (e : X ≅ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : e.hom ≫ g = f) : e.inv ≫ f = g := by
  exact (congrArg (fun a => e.inv ≫ a) h.symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ g) e.inv_hom_id).trans (Category.id_comp g)))

section Transport

variable (K : Type u) [Field K] {X Y : Scheme.{u}}
  (fX : X ⟶ Spec (.of K)) (fY : Y ⟶ Spec (.of K))
  [IsProper fX] [IsCurve K fX] [Smooth fX]
  [IsProper fY] [IsCurve K fY] [Smooth fY]
  (lX : X ⟶ space K) (lY : Y ⟶ space K)

/-- Actual over-field and over-LG triangles, with the original
quotient-pullback comparison constructed internally, transport one
side's genuine canonical generated complete Semi property. -/
theorem quotient_property_of_overIso (e : X ≅ Y)
    (hb : e.hom ≫ fY = fX) (hl : e.hom ≫ lY = lX)
    (hY : MukaiCanonicalBundleFromNet.IsCanonicalGeneratedSemi fY (bundle K lY)) :
    MukaiCanonicalBundleFromNet.IsCanonicalGeneratedSemi fX (bundle K lX) := by
  have hP := MukaiCanonicalBundleIsoTransport.isCanonicalGeneratedSemi_pullback
    K fX fY e hb (bundle K lY) hY
  exact MukaiCanonicalModuleIsoTransport.isCanonicalGeneratedSemi_of_iso K fX
    (LagrangianSectionZeroBoundApplications.quotientIso K lX lY e.hom hl) hP

end Transport

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]

section Ordered

variable (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  [IsIntegral (LagrangianTransverseRestriction.curve K M)]
  [SmoothOfRelativeDimension 1 (LagrangianTransverseRestriction.curveProjection K M)]

include hM

/-- The literal original ordered section's quotient is the genuine
canonical Mukai bundle when THIS actual curve is genus nine and has
no degree-five pencil. Its model and both geometric comparisons are
derived, not assumptions. -/
theorem ordered_isCanonicalGeneratedSemi
    (hdim : topologicalKrullDim (LagrangianTransverseRestriction.curve K M) ≤ 1)
    (hg : genus (LagrangianTransverseRestriction.curveProjection K M) = 9)
    (hnp : ¬ Nonempty (LinearSeries K (LagrangianTransverseRestriction.curveProjection K M)
      hdim 5 1)) :
    MukaiCanonicalBundleFromNet.IsCanonicalGeneratedSemi
      (LagrangianTransverseRestriction.curveProjection K M)
      (bundle K (LagrangianTransverseRestriction.inclusion K M)) := by
  let fX := LagrangianTransverseRestriction.curveProjection K M
  let fY := LagrangianOrderedFibre.modelProjection K M hM
  let lX := LagrangianTransverseRestriction.inclusion K M
  let lY := LagrangianOrderedFibre.modelInclusion K M hM
  have hgood := LagrangianTransverseGoodOpen.matrixPoint_lands_goodOpen K M hM
    (IsLocalRing.closedPoint K)
  letI := LagrangianGoodOpenRestriction.model_integral K M hM hgood
  letI := LagrangianGoodOpenRestriction.model_smooth K M hM hgood
  letI := LagrangianRankTwoSubsystemBundles.model_isCurve K M hM
  letI : Smooth fX := SmoothOfRelativeDimension.smooth 1 fX
  letI : Smooth fY := SmoothOfRelativeDimension.smooth 1 fY
  let e := LagrangianOrderedFibre.cutIsoModel K M hM
  have hb : e.hom ≫ fY = fX := LagrangianOrderedFibre.cutIsoModel_hom_base K M hM
  have hl : e.hom ≫ lY = lX := LagrangianOrderedFibre.cutIsoModel_hom_toLG K M hM
  let hY : topologicalKrullDim (LagrangianOrderedFibre.model K M hM) ≤ 1 :=
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension fY 1).le
  have hgY : genus fY = 9 := (MukaiCurveIsoLinearSeries.genus_eq K fX fY e hb).symm.trans hg
  have hnY : ¬ Nonempty (LinearSeries K fY hY 5 1) :=
    (MukaiCurveIsoLinearSeries.no_degree_five_pencil_iff K fX fY e hb hdim hY).mp hnp
  have hQY := LagrangianNonpentagonalQuotientFactory.isCanonicalGeneratedSemi_of_no_degree_five
    K M hM hgY hnY
  exact quotient_property_of_overIso K fX fY lX lY e hb hl hQY

end Ordered

section MatrixFibre

open LagrangianLinearSections LagrangianMatrixPointRows LagrangianGeometricFibre

variable (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  (hgood : matrixPoint K M hM (IsLocalRing.closedPoint K) ∈
    LagrangianLinearSectionGenericSmooth.goodOpen K)

include hgood

/-- The SAME original geometric incidence fibre and its SAME original
universal quotient have the complete canonical property; curve genus
and no-pencil are the only extra curve conditions. -/
theorem matrixFibre_isCanonicalGeneratedSemi
    (hdim : topologicalKrullDim (geometricFibre K M hM) ≤ 1)
    (hg : genus (pullback.snd (familyProjection K) (matrixPoint K M hM)) = 9)
    (hnp : ¬ Nonempty (LinearSeries K
      (pullback.snd (familyProjection K) (matrixPoint K M hM)) hdim 5 1)) :
    MukaiCanonicalBundleFromNet.IsCanonicalGeneratedSemi
      (pullback.snd (familyProjection K) (matrixPoint K M hM))
      (bundle K (geometricFibreToLG K M hM)) := by
  let fX := LagrangianTransverseRestriction.curveProjection K M
  let fY := pullback.snd (familyProjection K) (matrixPoint K M hM)
  let lX := LagrangianTransverseRestriction.inclusion K M
  let lY := geometricFibreToLG K M hM
  letI := LagrangianGoodOpenRestriction.model_integral K M hM hgood
  letI := LagrangianGoodOpenRestriction.model_smooth K M hM hgood
  letI := LagrangianModelRestriction.ordered_integral K M hM
  letI := LagrangianModelRestriction.ordered_smooth K M hM
  letI := LagrangianGoodOpenRestriction.fibre_integral K M hM hgood
  letI : SmoothOfRelativeDimension 1 fY := LagrangianGoodOpenRestriction.fibre_smooth K M hM hgood
  letI : IsCurve K fY := by
    exact (isCurve_iff K fY).mpr
      ⟨⟨⟩,topologicalKrullDim_eq_of_smoothOfRelativeDimension fY 1⟩
  letI : Smooth fX := SmoothOfRelativeDimension.smooth 1 fX
  letI : Smooth fY := SmoothOfRelativeDimension.smooth 1 fY
  let e := LagrangianOrderedFibre.cutIsoFibre K M hM
  have hb : e.hom ≫ fY = fX := LagrangianOrderedFibre.cutIsoFibre_hom_base K M hM
  have hl : e.hom ≫ lY = lX := LagrangianOrderedFibre.cutIsoFibre_hom_toLG K M hM
  let hX : topologicalKrullDim (LagrangianTransverseRestriction.curve K M) ≤ 1 :=
    (topologicalKrullDim_eq_of_smoothOfRelativeDimension fX 1).le
  have hgX : genus fX = 9 := (MukaiCurveIsoLinearSeries.genus_eq K fX fY e hb).trans hg
  have hnX : ¬ Nonempty (LinearSeries K fX hX 5 1) :=
    (MukaiCurveIsoLinearSeries.no_degree_five_pencil_iff K fX fY e hb hX hdim).mpr hnp
  have hQX := ordered_isCanonicalGeneratedSemi K M hM hX hgX hnX
  exact quotient_property_of_overIso K fY fX lY lX e.symm
    (inverse_triangle e fX fY hb) (inverse_triangle e lX lY hl) hQX

end MatrixFibre

section RationalPoint

open LagrangianLinearSections LagrangianLinearSectionGenericSmooth

/-- Every actual original rational parameter on the good open has the
property under its OWN true genus-nine/no-pencil conditions. The actual
surjective matrix is constructed internally; no model or quotient
comparison is an input. -/
theorem rationalPoint_isCanonicalGeneratedSemi
    (p : Spec (.of K) ⟶ parameter K) (hp : p ≫ parameterProjection K = 𝟙 _)
    (hgood : p (IsLocalRing.closedPoint K) ∈ goodOpen K)
    (hdim : topologicalKrullDim (pullback (C := Scheme.{u}) (familyProjection K) p) ≤ 1)
    (hg : genus (pullback.snd (familyProjection K) p) = 9)
    (hnp : ¬ Nonempty (LinearSeries K (pullback.snd (familyProjection K) p) hdim 5 1)) :
    MukaiCanonicalBundleFromNet.IsCanonicalGeneratedSemi (pullback.snd (familyProjection K) p)
      (bundle K (pullback.fst (familyProjection K) p ≫ familyToLG K)) := by
  obtain ⟨M,hM,rfl⟩ := LagrangianParameterMatrix.exists_matrix K p hp
  exact matrixFibre_isCanonicalGeneratedSemi K M hM hgood hdim hg hnp

end RationalPoint

end M9Native.LagrangianQuotientFactoryApplications
