module

public import M9StacksIntegration.LagrangianUniversalSectionZeroBound
public import M9StacksIntegration.LagrangianTransverseGoodOpen
public import M9StacksIntegration.LagrangianModelRestriction
public import M9StacksIntegration.LagrangianParameterMatrix
public import M9StacksIntegration.LagrangianTripleNaturality
public import M9StacksIntegration.FiniteFreeBasisPullback
public import M9StacksIntegration.NativeVectorSectionZeroTransport

/-! The full section-zero and canonical hyperplane sheaf-cokernel bounds
on the actual ordered transverse cut, its literal five-section model,
and every original rational good-open parameter. Quotient, constant
section, full native zero-scheme, and original-field cohomology
comparisons are derived internally. No model, zero-iso, finiteness,
length, genus, or cohomology-bound premise is supplied to the clients. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open scoped BigOperators
universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.LagrangianSectionZeroBoundApplications

open AlgebraicGeometry.Grassmannian LagrangianMatrixChart
open LagrangianUniversalSections LagrangianHyperplaneEvaluation

attribute [local instance] bundle_rank bundle_finiteLocallyFree

section Transport

variable (K : Type u) [Field K] {X Y : Scheme.{u}}
  (fX : X ⟶ Spec (.of K)) (fY : Y ⟶ Spec (.of K))
  (lX : X ⟶ LagrangianGrassmannian.space K)
  (lY : Y ⟶ LagrangianGrassmannian.space K)

theorem exists_quotientIso (g : X ⟶ Y) (hl : g ≫ lY = lX) :
    ∃ a : (Scheme.Modules.pullback g).obj (bundle K lY) ≅ bundle K lX,
      (pullbackPresentation g (quotient K lY)).map ≫ a.hom = quotientMap K lX := by
  have h : (pullbackPresentation g (quotient K lY)).Isomorphic (quotient K lX) := by
    simpa only [quotient, hl] using
      LagrangianPluckerTrivialization.pullbackPresentation_comp_isomorphic
        lY g (LagrangianPluckerQuotient.quotientOnLG K)
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha⟩

def quotientIso (g : X ⟶ Y) (hl : g ≫ lY = lX) :
    (Scheme.Modules.pullback g).obj (bundle K lY) ≅ bundle K lX :=
  Classical.choose (exists_quotientIso K lX lY g hl)

theorem quotientIso_triangle (g : X ⟶ Y) (hl : g ≫ lY = lX) :
    (pullbackPresentation g (quotient K lY)).map ≫ (quotientIso K lX lY g hl).hom =
      quotientMap K lX :=
  Classical.choose_spec (exists_quotientIso K lX lY g hl)

theorem quotientIso_section (g : X ⟶ Y) (hl : g ≫ lY = lX)
    (hf : g ≫ fY = fX) (v : Fin 6 → K) :
    (quotientIso K lX lY g hl).hom.app ⊤
      (pullbackGlobalSections g (bundle K lY) (originalSection K fY lY v)) =
        originalSection K fX lX v := by
  have hb (i : Fin 6) : (quotientIso K lX lY g hl).hom.app ⊤
      (pullbackGlobalSections g (bundle K lY)
        ((quotientMap K lY).app ⊤ (freeBasisSection Y 6 i))) =
      (quotientMap K lX).app ⊤ (freeBasisSection X 6 i) := by
    have h := congrArg (fun a : freeOn X 6 ⟶ bundle K lX =>
      a.app ⊤ (freeBasisSection X 6 i)) (quotientIso_triangle K lX lY g hl)
    change (quotientIso K lX lY g hl).hom.app ⊤
      (Scheme.Modules.Hom.app (X := X) (pullbackPresentation g (quotient K lY)).map
        ⊤ (freeBasisSection X 6 i)) = _ at h
    rw [FiniteFreeBasisPullback.pullbackPresentation_basis] at h
    exact h
  simp only [originalSection, constantVector, map_sum, Scheme.Modules.Hom.app_smul,
    SectionsEqualizer.pullbackGlobalSections_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hb i]
  apply congrArg (fun a => a • (quotientMap K lX).app ⊤ (freeBasisSection X 6 i))
  have h := RingHom.congr_fun (LagrangianTripleNaturality.baseRingMap_comp K fY g) (v i)
  simpa only [hf, RingHom.comp_apply] using h.symm

/-- The actual LG and original-field triangles induce an actual
isomorphism of the full native zero schemes, including nilpotents. -/
def zeroIso (e : X ≅ Y) (hl : e.hom ≫ lY = lX) (hf : e.hom ≫ fY = fX)
    (v : Fin 6 → K) :
    (zeroIdeal K fX lX v).subscheme ≅ (zeroIdeal K fY lY v).subscheme :=
  NativeVectorSectionZeroTransport.zeroSchemeIso (bundle K lY) (bundle K lX) 3 e
    (quotientIso K lX lY e.hom hl) (originalSection K fY lY v) (originalSection K fX lX v)
    (quotientIso_section K fX fY lX lY e.hom hl hf v)

/-- The full zero-scheme comparison preserves the original field map. -/
theorem zeroIso_over (e : X ≅ Y) (hl : e.hom ≫ lY = lX) (hf : e.hom ≫ fY = fX)
    (v : Fin 6 → K) :
    (zeroIso K fX fY lX lY e hl hf v).hom ≫ zeroProjection K fY lY v =
      zeroProjection K fX lX v :=
  NativeVectorSectionZeroTransport.zeroSchemeIso_over (bundle K lY) (bundle K lX) 3 e
    (quotientIso K lX lY e.hom hl) (originalSection K fY lY v) (originalSection K fX lX v)
    (quotientIso_section K fX fY lX lY e.hom hl hf v) fX fY hf

/-- True original-field H0 transport on the full native section zero. -/
theorem zero_H0_eq (e : X ≅ Y) (hl : e.hom ≫ lY = lX) (hf : e.hom ≫ fY = fX)
    (v : Fin 6 → K) :
    finrank K (structureSheafCohomology (zeroProjection K fX lX v) 0) =
      finrank K (structureSheafCohomology (zeroProjection K fY lY v) 0) :=
  (SplitQuadricQuotientCoordinates.structureCohomologyIso K
    (zeroIso K fX fY lX lY e hl hf v) (zeroProjection K fX lX v)
    (zeroProjection K fY lY v) (zeroIso_over K fX fY lX lY e hl hf v) 0).toLinearEquiv.finrank_eq

end Transport

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]

section Ordered

variable (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  [IsIntegral (LagrangianTransverseRestriction.curve K M)]
  [SmoothOfRelativeDimension 1 (LagrangianTransverseRestriction.curveProjection K M)]

include hM

/-- Mukai II4.4(1) on the literal original ordered transverse cut. -/
theorem ordered_zero_H0_le_two (v : Fin 6 → K) (hv : v ≠ 0) :
    finrank K (structureSheafCohomology
      (zeroProjection K (LagrangianTransverseRestriction.curveProjection K M)
        (LagrangianTransverseRestriction.inclusion K M) v) 0) ≤ 2 := by
  have h := zero_H0_eq K (LagrangianTransverseRestriction.curveProjection K M)
    (LagrangianStandardSectionZeroModel.curveProjection K M hM)
    (LagrangianTransverseRestriction.inclusion K M) (LagrangianStandardSectionZeroModel.toLG K M hM)
    (LagrangianOrderedFibre.cutIsoFibre K M hM)
    (LagrangianOrderedFibre.cutIsoFibre_hom_toLG K M hM)
    (LagrangianOrderedFibre.cutIsoFibre_hom_base K M hM) v
  exact h.trans_le (LagrangianUniversalSectionZeroBound.goodOpen_zero_h0_le_two K M hM
    (LagrangianTransverseGoodOpen.matrixPoint_lands_goodOpen K M hM (IsLocalRing.closedPoint K)) v hv)

/-- Mukai II4.4(2) on the actual original hyperplane evaluation SHEAF
cokernel, whose H0 is compared with the same full native zero scheme. -/
theorem ordered_hyperplaneCokernel_H0_le_two (v : Fin 6 → K) (hv : v ≠ 0) :
    finrank K (cohomologyOverField K (LagrangianTransverseRestriction.curveProjection K M)
      (hyperplaneCokernel K (LagrangianTransverseRestriction.curveProjection K M)
        (LagrangianTransverseRestriction.inclusion K M) v) 0) ≤ 2 :=
  (LagrangianHyperplaneZeroCokernel.finrank_hyperplaneCokernel_H0 K
    (LagrangianTransverseRestriction.curveProjection K M)
    (LagrangianTransverseRestriction.inclusion K M) v hv).trans_le
      (ordered_zero_H0_le_two K M hM v hv)

end Ordered

section Model

variable (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  [IsIntegral (LagrangianOrderedFibre.model K M hM)]
  [SmoothOfRelativeDimension 1 (LagrangianOrderedFibre.modelProjection K M hM)]

/-- The same full-J bound on the literal five-section bundle model;
its ordered comparison and good-open geometry are derived internally. -/
theorem model_zero_H0_le_two (v : Fin 6 → K) (hv : v ≠ 0) :
    finrank K (structureSheafCohomology
      (zeroProjection K (LagrangianOrderedFibre.modelProjection K M hM)
        (LagrangianOrderedFibre.modelInclusion K M hM) v) 0) ≤ 2 := by
  let : IsIntegral (LagrangianTransverseRestriction.curve K M) :=
    LagrangianModelRestriction.ordered_integral K M hM
  let : SmoothOfRelativeDimension 1 (LagrangianTransverseRestriction.curveProjection K M) :=
    LagrangianModelRestriction.ordered_smooth K M hM
  have hb : (LagrangianOrderedFibre.modelIsoFibre K M hM).hom ≫
      LagrangianStandardSectionZeroModel.curveProjection K M hM =
        LagrangianOrderedFibre.modelProjection K M hM := by
    change (LagrangianOrderedFibre.modelIsoFibre K M hM).hom ≫
      pullback.snd (LagrangianLinearSections.familyProjection K)
        (LagrangianMatrixPointRows.matrixPoint K M hM) =
      LagrangianOrderedFibre.modelInclusion K M hM ≫ LagrangianGrassmannian.projection K
    rw [← LagrangianOrderedFibre.geometricFibre_over K M hM, ← Category.assoc,
      LagrangianOrderedFibre.modelIsoFibre_hom_toLG K M hM]
  have h := zero_H0_eq K (LagrangianOrderedFibre.modelProjection K M hM)
    (LagrangianStandardSectionZeroModel.curveProjection K M hM)
    (LagrangianOrderedFibre.modelInclusion K M hM) (LagrangianStandardSectionZeroModel.toLG K M hM)
    (LagrangianOrderedFibre.modelIsoFibre K M hM)
    (LagrangianOrderedFibre.modelIsoFibre_hom_toLG K M hM) hb v
  exact h.trans_le (LagrangianUniversalSectionZeroBound.goodOpen_zero_h0_le_two K M hM
    (LagrangianTransverseGoodOpen.matrixPoint_lands_goodOpen K M hM (IsLocalRing.closedPoint K)) v hv)

/-- The genuine native hyperplane sheaf-cokernel bound on the actual
five-section model, with no supplied model or zero-scheme comparison. -/
theorem model_hyperplaneCokernel_H0_le_two (v : Fin 6 → K) (hv : v ≠ 0) :
    finrank K (cohomologyOverField K (LagrangianOrderedFibre.modelProjection K M hM)
      (hyperplaneCokernel K (LagrangianOrderedFibre.modelProjection K M hM)
        (LagrangianOrderedFibre.modelInclusion K M hM) v) 0) ≤ 2 :=
  (LagrangianHyperplaneZeroCokernel.finrank_hyperplaneCokernel_H0 K
    (LagrangianOrderedFibre.modelProjection K M hM)
    (LagrangianOrderedFibre.modelInclusion K M hM) v hv).trans_le
      (model_zero_H0_le_two K M hM v hv)

end Model

section RationalParameter

open LagrangianLinearSections LagrangianLinearSectionGenericSmooth

variable (p : Spec (.of K) ⟶ parameter K) (hp : p ≫ parameterProjection K = 𝟙 _)
  (hg : p (IsLocalRing.closedPoint K) ∈ goodOpen K)

include hp hg

/-- Every actual original rational good-open parameter has the full-J
bound; its true surjective coefficient matrix is constructed internally. -/
theorem rationalPoint_zero_H0_le_two (v : Fin 6 → K) (hv : v ≠ 0) :
    finrank K (structureSheafCohomology
      (zeroProjection K (pullback.snd (familyProjection K) p)
        (pullback.fst (familyProjection K) p ≫ familyToLG K) v) 0) ≤ 2 := by
  obtain ⟨M, hM, rfl⟩ := LagrangianParameterMatrix.exists_matrix K p hp
  exact LagrangianUniversalSectionZeroBound.goodOpen_zero_h0_le_two K M hM hg v hv

/-- The actual canonical hyperplane SHEAF cokernel has H0 at most two
on every original rational good-open point, without a chosen matrix. -/
theorem rationalPoint_hyperplaneCokernel_H0_le_two (v : Fin 6 → K) (hv : v ≠ 0) :
    finrank K (cohomologyOverField K (pullback.snd (familyProjection K) p)
      (hyperplaneCokernel K (pullback.snd (familyProjection K) p)
        (pullback.fst (familyProjection K) p ≫ familyToLG K) v) 0) ≤ 2 := by
  obtain ⟨M, hM, rfl⟩ := LagrangianParameterMatrix.exists_matrix K p hp
  exact LagrangianUniversalSectionZeroBound.goodOpen_hyperplaneCokernel_H0_le_two K M hM hg v hv

end RationalParameter

end M9Native.LagrangianSectionZeroBoundApplications
