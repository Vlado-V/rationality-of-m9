module

public import M9StacksIntegration.LagrangianGoodPointCriterion
public import M9StacksIntegration.OpenRestrictionPointFiber
public import M9StacksIntegration.LagrangianTransverseRestriction
public import M9StacksIntegration.LagrangianOrderedFibre
public import M9StacksIntegration.LagrangianLinearSectionGenericSmooth
public import M9StacksIntegration.UniversalLagrangianFieldGenus
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange

/-! Every actual integral smooth transverse ordered cut lies in the
canonical good parameter open. Its actual curve is identified with the
original restricted family's field fibre, retaining the original base
projection. No good-open membership or genus hypothesis is supplied. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1400000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

namespace M9Native.LagrangianTransverseGoodOpen
open LagrangianTransverseRestriction LagrangianOrderedFibre
open LagrangianLinearSections LagrangianLinearSectionGenericSmooth
open LagrangianGeometricFibre LagrangianMatrixPointRows

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K)
  [IsIntegral (curve K M)] [SmoothOfRelativeDimension 1 (curveProjection K M)]

omit [IsAlgClosed K] in
theorem matrixPoint_lands_goodOpen (hM : Function.Surjective M.mulVec) :
    ∀ t : Spec (.of K), matrixPoint K M hM t ∈ goodOpen K := by
  let e : curve K M ≅ geometricFibre K M hM := cutIsoFibre K M hM
  let q := pullback.snd (familyProjection K) (matrixPoint K M hM)
  have hb : e.hom ≫ q = curveProjection K M := cutIsoFibre_hom_base K M hM
  have hbi : e.inv ≫ curveProjection K M = q := by
    rw [← hb, Iso.inv_hom_id_assoc]
  letI : Smooth (curveProjection K M) := SmoothOfRelativeDimension.smooth 1 _
  letI : Smooth q := by rw [← hbi]; infer_instance
  letI : IrreducibleSpace (geometricFibre K M hM) :=
    (Scheme.homeoOfIso e).irreducibleSpace_iff.mp inferInstance
  have hdim : topologicalKrullDim (geometricFibre K M hM) = 1 :=
    (IsHomeomorph.topologicalKrullDim_eq (Scheme.homeoOfIso e)
      (Scheme.homeoOfIso e).isHomeomorph).symm.trans
        (IsCurve.topologicalKrullDim_eq_one (f := curveProjection K M))
  exact LagrangianGoodPointCriterion.matrixPoint_lands_goodOpen K M hM hdim

def goodParameter (hM : Function.Surjective M.mulVec) :
    Spec (.of K) ⟶ (goodOpen K).toScheme :=
  OpenRestrictionPointFiber.lift (goodOpen K) (matrixPoint K M hM)
    (matrixPoint_lands_goodOpen K M hM)

@[reassoc] theorem goodParameter_comp (hM : Function.Surjective M.mulVec) :
    goodParameter K M hM ≫ (goodOpen K).ι = matrixPoint K M hM :=
  OpenRestrictionPointFiber.lift_comp _ _ _

def curveIsoRestrictedFibre (hM : Function.Surjective M.mulVec) :
    curve K M ≅ pullback (restrictedProjection K) (goodParameter K M hM) :=
  cutIsoFibre K M hM ≪≫
    (OpenRestrictionPointFiber.fiberIso (familyProjection K) (goodOpen K)
      (matrixPoint K M hM) (matrixPoint_lands_goodOpen K M hM)).symm

@[reassoc] theorem curveIsoRestrictedFibre_hom_base (hM : Function.Surjective M.mulVec) :
    (curveIsoRestrictedFibre K M hM).hom ≫
      pullback.snd (restrictedProjection K) (goodParameter K M hM) = curveProjection K M := by
  have h := OpenRestrictionPointFiber.fiberIso_hom_snd (familyProjection K) (goodOpen K)
    (matrixPoint K M hM) (matrixPoint_lands_goodOpen K M hM)
  change ((cutIsoFibre K M hM).hom ≫
    (OpenRestrictionPointFiber.fiberIso (familyProjection K) (goodOpen K)
      (matrixPoint K M hM) (matrixPoint_lands_goodOpen K M hM)).inv) ≫
    pullback.snd (familyProjection K ∣_ goodOpen K)
      (OpenRestrictionPointFiber.lift (goodOpen K) (matrixPoint K M hM)
        (matrixPoint_lands_goodOpen K M hM)) = _
  rw [Category.assoc,← h,Iso.inv_hom_id_assoc]
  exact cutIsoFibre_hom_base K M hM

/-- The true genus of the original arbitrary transverse cut is the
computed genus of the unchanged original universal family. -/
theorem genus_eq_fibreGenus (hM : Function.Surjective M.mulVec) :
    genus (curveProjection K M) = UniversalLagrangianNativeGenus.fibreGenus K := by
  let e := curveIsoRestrictedFibre K M hM
  let p := pullback.snd (restrictedProjection K) (goodParameter K M hM)
  have hbase : e.hom ≫ p = curveProjection K M := curveIsoRestrictedFibre_hom_base K M hM
  have h : genus (curveProjection K M) = genus p := by
    apply genus_baseChange K K e.hom (curveProjection K M) p
    rw [show Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (.of K)) by simp]
    exact IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using hbase⟩
  exact h.trans (UniversalLagrangianFieldGenus.field_genus_eq_fibreGenus K
    (goodParameter K M hM))

/-- The original arbitrary integral smooth ordered cut satisfies the
actual LG-degree/genus relation, before any numerical LG-degree input. -/
theorem genus_degree_relation (hM : Function.Surjective M.mulVec) :
    2 * (genus (curveProjection K M) : ℤ) - 2 =
      degreeWithRespectTo K (LagrangianGrassmannian.projection K)
        (𝟙 (LagrangianGrassmannian.space K)) 6 (LagrangianIntegral.space_dimension K)
        (LagrangianPluckerQuotient.determinantLine K)
        (LagrangianDegree.determinantLine_modulesIsAmple K) := by
  rw [genus_eq_fibreGenus K M hM]
  exact LagrangianFiveCutCanonical.family_genus_degree_relation K

end M9Native.LagrangianTransverseGoodOpen
