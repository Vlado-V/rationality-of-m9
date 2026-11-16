module

public import M9StacksIntegration.SmoothIntegralHyperplaneCuts
public import M9StacksIntegration.LagrangianGeometricFibre
public import M9StacksIntegration.LagrangianGoodPointCriterion

/-! The actual five successive Bertini cuts are an actual original
universal-incidence point fibre. The comparison is proved on all test
schemes using the original determinant sections, and retains the base
projection. Thus the constructed point lies in the canonical good open. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.LagrangianBertiniPoint

open SmoothIntegralHyperplaneCuts LagrangianLinearSections
open LagrangianGeometricFibre IteratedLineSectionCuts
variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]

/-- Exact all-test equivalence between the actual five cuts and the
actual original incidence fibre at their actual rank-five parameter. -/
theorem factorization_iff {T : Scheme.{u}} (f : T ⟶ LagrangianGrassmannian.space K) :
    (∃ g : T ⟶ fiveCutCurve K, g ≫ fiveCutToLG K = f) ↔
      (∃ g : T ⟶ geometricFibre K (coefficientMatrix K) (coefficientMatrix_surjective K),
        g ≫ geometricFibreToLG K (coefficientMatrix K) (coefficientMatrix_surjective K) = f) := by
  rw [fiveCut_factors_iff_determinantSection, geometricFibre_factorsThrough_iff_rows]
  apply forall_congr'
  intro j
  exact LagrangianHyperplaneRows.pullback_row_zero_iff K f (coefficientMatrix K) j

/-- The actual successive-cut curve is the actual original fibre,
including its scheme structure. -/
def cutIsoPointFibre : fiveCutCurve K ≅
    pullback (C := Scheme.{u}) (familyProjection K) (parameterPoint K) := by
  let A : Over (LagrangianGrassmannian.space K) := Over.mk (fiveCutToLG K)
  let B : Over (LagrangianGrassmannian.space K) :=
    Over.mk (geometricFibreToLG K (coefficientMatrix K) (coefficientMatrix_surjective K))
  let : IsClosedImmersion A.hom := (fifthState K).closed
  let : Mono A.hom := inferInstance
  let : Mono B.hom := by
    have : IsClosedImmersion (geometricFibreToLG K (coefficientMatrix K)
        (coefficientMatrix_surjective K)) := by
      rw [← geometricFibreIsoSection_hom_toLG]
      infer_instance
    change Mono (geometricFibreToLG K (coefficientMatrix K) (coefficientMatrix_surjective K))
    infer_instance
  exact comparisonIso A B (fun _T f => factorization_iff K f)

@[reassoc]
theorem cutIsoPointFibre_hom_toLG :
    (cutIsoPointFibre K).hom ≫ pullback.fst (familyProjection K) (parameterPoint K) ≫
      familyToLG K = fiveCutToLG K :=
  comparisonHom_comp (Over.mk (fiveCutToLG K))
    (Over.mk (geometricFibreToLG K (coefficientMatrix K) (coefficientMatrix_surjective K)))
    (fun _T f => factorization_iff K f)

@[reassoc]
theorem cutIsoPointFibre_hom_base :
    (cutIsoPointFibre K).hom ≫ pullback.snd (familyProjection K) (parameterPoint K) =
      fiveCutToLG K ≫ LagrangianGrassmannian.projection K := by
  have hb : pullback.fst (familyProjection K) (parameterPoint K) ≫ familyToLG K ≫
      LagrangianGrassmannian.projection K =
        pullback.snd (familyProjection K) (parameterPoint K) := by
    calc
      _ = pullback.fst (familyProjection K) (parameterPoint K) ≫
          (familyProjection K ≫ parameterProjection K) :=
        congrArg (fun h => pullback.fst (familyProjection K) (parameterPoint K) ≫ h)
          (family_over K)
      _ = (pullback.fst (familyProjection K) (parameterPoint K) ≫ familyProjection K) ≫
          parameterProjection K := (Category.assoc _ _ _).symm
      _ = (pullback.snd (familyProjection K) (parameterPoint K) ≫ parameterPoint K) ≫
          parameterProjection K :=
        congrArg (fun h => h ≫ parameterProjection K)
          (pullback.condition (f := familyProjection K) (g := parameterPoint K))
      _ = _ := by
        rw [Category.assoc, parameterPoint_projection, Category.comp_id]
  rw [← hb]
  exact cutIsoPointFibre_hom_toLG_assoc K (LagrangianGrassmannian.projection K)

/-- The literal original incidence point-fibre morphism is smooth,
transported from the genuine constructed cut curve over the original base. -/
instance pointFibre_smooth : Smooth (pullback.snd (familyProjection K) (parameterPoint K)) := by
  let e := cutIsoPointFibre K
  have hs : Smooth (fiveCutToLG K ≫ LagrangianGrassmannian.projection K) := by
    rw [← initialSystem_toBase K]
    exact fiveCutCurve_smooth K
  let := hs
  have he : e.inv ≫ (fiveCutToLG K ≫ LagrangianGrassmannian.projection K) =
      pullback.snd (familyProjection K) (parameterPoint K) := by
    rw [← cutIsoPointFibre_hom_base K, ← Category.assoc]
    simp only [e, Iso.inv_hom_id, Category.id_comp]
  rw [← he]
  infer_instance

/-- The literal original point fibre is irreducible, derived from the
genuine integral cut curve. -/
instance pointFibre_irreducible :
    IrreducibleSpace (pullback (C := Scheme.{u}) (familyProjection K) (parameterPoint K)) := by
  let : IsIntegral (fiveCutCurve K) := fiveCutCurve_integral K
  exact (Scheme.homeoOfIso (cutIsoPointFibre K)).irreducibleSpace_iff.mp inferInstance

/-- The literal original point fibre has its genuine computed dimension one. -/
theorem pointFibre_dimension :
    topologicalKrullDim (pullback (C := Scheme.{u}) (familyProjection K) (parameterPoint K)) = 1 := by
  let e := Scheme.homeoOfIso (cutIsoPointFibre K)
  exact (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).symm.trans
    (fiveCutCurve_dimension K)

/-- The actual parameter constructed from the genuine five cuts lies
in the original canonical proper smooth open; no smooth-open premise. -/
theorem parameterPoint_lands_goodOpen :
    ∀ t : Spec (.of K), parameterPoint K t ∈ ProperSmoothLocus.goodOpen (familyProjection K) :=
  LagrangianGoodPointCriterion.fieldPoint_lands_goodOpen K (parameterPoint K)
    (parameterPoint_projection K) (pointFibre_dimension K)

end M9Native.LagrangianBertiniPoint
