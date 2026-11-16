module

public import M9StacksIntegration.GenusNineMukaiBundle
public import M9StacksIntegration.MukaiActualLinearSectionRecognition
public import M9StacksIntegration.LagrangianFibreIsoGoodOpen
public import M9StacksIntegration.OpenRestrictionPointFiber

@[expose] public section

/-!
# Every original nonpentagonal genus-nine curve is an original linear section

Actual Brill--Noether existence constructs the original canonical Mukai
bundle. Actual conormal invertibility and connectedness identify the
original curve with the entire original incidence fibre. Its genuine
good-open membership is derived from this isomorphism over the original
field. No bundle, net, basis, defining matrix, fibre isomorphism or
good-open membership is supplied as a premise.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace M9Native.GenusNineMukaiLinearSection

open MukaiPrimitiveCanonicalEvaluation LagrangianLinearSections

variable (K : Type u) [Field K] [CharZero K] [IsAlgClosed K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [IsCurve K f] [IsProper f] [Smooth f]

/-- The actual original curve is the entire original incidence fibre,
retaining the actual Mukai map and original base map. Every bundle and
matrix in the conclusion is constructed. -/
theorem exists_original_fibreIso
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries K f (IsCurve.topologicalKrullDim_eq_one f).le 5 1)) :
    ∃ (E : X.Modules) (n : NormalizedEvaluation K f E)
      (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
      (e : X ≅ LagrangianFibreFactorization.fibre K
        (LagrangianMatrixPointRows.matrixPoint K M hM)),
      MukaiCanonicalBundleFromNet.IsCanonicalGeneratedSemi f E ∧
      e.hom ≫ LagrangianFibreFactorization.fibreToLG K
        (LagrangianMatrixPointRows.matrixPoint K M hM) = n.diagram.map ∧
      e.hom ≫ pullback.fst (LagrangianMatrixPointRows.matrixPoint K M hM)
        (familyProjection K) = f := by
  obtain ⟨E,hE,_⟩ := GenusNineMukaiBundle.exists_unique_canonical_generated_semi K f hg hnp
  obtain ⟨hr,h6,⟨c⟩,hgen,hsemi⟩ := hE
  letI := hr
  obtain ⟨n,M,hM,e,hLG,hbase⟩ :=
    MukaiActualLinearSectionRecognition.exists_fibreIso K f E c hg hgen h6 hsemi hnp
  exact ⟨E,n,M,hM,e,⟨hr,h6,⟨c⟩,hgen,hsemi⟩,hLG,hbase⟩

/-- A genuine original parameter in the canonical good open and its
entire original conventional incidence fibre realize the curve over K.
The parameter, membership and whole-fibre isomorphism are conclusions. -/
theorem exists_good_fibreIso
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries K f (IsCurve.topologicalKrullDim_eq_one f).le 5 1)) :
    ∃ (p : Spec (.of K) ⟶ parameter K)
      (_hp : p ≫ parameterProjection K = 𝟙 _)
      (_hgood : ∀ t : Spec (.of K), p t ∈ LagrangianLinearSectionGenericSmooth.goodOpen K)
      (e : X ≅ pullback (familyProjection K) p),
      e.hom ≫ pullback.snd (familyProjection K) p = f := by
  obtain ⟨E,n,M,hM,e,_,_,hb⟩ := exists_original_fibreIso K f hg hnp
  let p := LagrangianMatrixPointRows.matrixPoint K M hM
  have hp : p ≫ parameterProjection K = 𝟙 _ :=
    SplitMatrixGrassmannian.fieldPoint_projection 9 14 K M hM
  have hgood := LagrangianFibreIsoGoodOpen.lands_goodOpen_of_original_iso K f p hp e hb
  refine ⟨p,hp,hgood,e ≪≫ pullbackSymmetry p (familyProjection K),?_⟩
  simpa only [Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd] using hb

/-- The constructed parameter is an actual map into the original good
parameter scheme. Its restricted-family fibre is the entire original
curve, with both the original parameter and field triangles. -/
theorem exists_goodParameterMap_fibreIso
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries K f (IsCurve.topologicalKrullDim_eq_one f).le 5 1)) :
    ∃ (p : Spec (.of K) ⟶ parameter K)
      (pGood : Spec (.of K) ⟶ (LagrangianLinearSectionGenericSmooth.goodOpen K).toScheme)
      (e : X ≅ pullback (LagrangianLinearSectionGenericSmooth.restrictedProjection K) pGood),
      pGood ≫ (LagrangianLinearSectionGenericSmooth.goodOpen K).ι = p ∧
      p ≫ parameterProjection K = 𝟙 _ ∧
      e.hom ≫ pullback.snd (LagrangianLinearSectionGenericSmooth.restrictedProjection K)
        pGood = f := by
  obtain ⟨p,hp,hgood,e,hbase⟩ := exists_good_fibreIso K f hg hnp
  let pGood := OpenRestrictionPointFiber.lift
    (LagrangianLinearSectionGenericSmooth.goodOpen K) p hgood
  let eF := OpenRestrictionPointFiber.fiberIso (familyProjection K)
    (LagrangianLinearSectionGenericSmooth.goodOpen K) p hgood
  refine ⟨p,pGood,e ≪≫ eF.symm,OpenRestrictionPointFiber.lift_comp _ _ _,hp,?_⟩
  have h := OpenRestrictionPointFiber.fiberIso_hom_snd (familyProjection K)
    (LagrangianLinearSectionGenericSmooth.goodOpen K) p hgood
  change (e.hom ≫ eF.inv) ≫
    pullback.snd (familyProjection K ∣_ LagrangianLinearSectionGenericSmooth.goodOpen K)
      (OpenRestrictionPointFiber.lift
        (LagrangianLinearSectionGenericSmooth.goodOpen K) p hgood) = f
  rw [Category.assoc, ← h, Iso.inv_hom_id_assoc]
  exact hbase

end M9Native.GenusNineMukaiLinearSection
