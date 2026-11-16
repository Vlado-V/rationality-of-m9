module

public import M9StacksIntegration.LagrangianPrimitiveSystem
public import M9StacksIntegration.LagrangianGeometricFibre
public import M9StacksIntegration.LagrangianFibreFiveSection

/-! The literal ordered five cuts, the original incidence fibre, and
the actual transported five-section model are isomorphic over the
original LG.  The comparison is derived on every test scheme, including
nonreduced schemes; no model-identification hypothesis is supplied. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianOrderedFibre

open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianPrimitiveSystem
open LagrangianLinearSections LagrangianMatrixPointRows LagrangianGeometricFibre
open LagrangianProjectiveSectionScheme IteratedLineSectionCuts

variable (K : Type u) [Field K] [CharZero K]
variable (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)

omit [CharZero K] in
theorem sectionCut_factorsThrough_iff_rows {T : Scheme.{u}} (l : T ⟶ space K) :
    FactorsThrough l (sectionCut K M) ↔
      ∀ j : Fin 5, pullbackGlobalSections l (determinantLine K)
        (LagrangianSymmetricPlucker.sectionLinear K
          (LagrangianProjectiveLinearForms.rowForms K M.mulVecLin j)) = 0 := by
  rw [sectionCut,simultaneousCut_factors_iff]
  change (∀ s ∈ List.ofFn (fun j : Fin 5 =>
    LagrangianHyperplaneCoordinates.determinantSection K (M j)),
      pullbackGlobalSections l (determinantLine K) s = 0) ↔ _
  rw [List.forall_mem_ofFn_iff]
  simp only [LagrangianHyperplaneRows.determinantSection_row]

theorem sectionCut_factorsThrough_iff_fibre {T : Scheme.{u}} (l : T ⟶ space K) :
    FactorsThrough l (sectionCut K M) ↔
      FactorsThrough l (Over.mk (geometricFibreToLG K M hM)) := by
  rw [sectionCut_factorsThrough_iff_rows]
  exact (geometricFibre_factorsThrough_iff_rows K M hM l).symm

instance fibreToLG_mono : Mono (geometricFibreToLG K M hM) := by
  have : IsClosedImmersion (geometricFibreToLG K M hM) := by
    rw [← geometricFibreIsoSection_hom_toLG K M hM]
    infer_instance
  infer_instance

/-- The original five ordered zero schemes are the actual original
universal incidence fibre, with their scheme structures retained. -/
def cutIsoFibre : (sectionCut K M).left ≅ geometricFibre K M hM := by
  let : IsClosedImmersion (sectionCut K M).hom := simultaneousCut_closed _ _
  let : Mono (sectionCut K M).hom := inferInstance
  let : Mono (Over.mk (geometricFibreToLG K M hM)).hom := by
    change Mono (geometricFibreToLG K M hM)
    infer_instance
  exact comparisonIso (sectionCut K M) (Over.mk (geometricFibreToLG K M hM))
    (fun _ l => sectionCut_factorsThrough_iff_fibre K M hM l)

@[reassoc] theorem cutIsoFibre_hom_toLG :
    (cutIsoFibre K M hM).hom ≫ geometricFibreToLG K M hM = (sectionCut K M).hom :=
  comparisonHom_comp (sectionCut K M) (Over.mk (geometricFibreToLG K M hM))
    (fun _ l => sectionCut_factorsThrough_iff_fibre K M hM l)

omit [CharZero K] in
theorem geometricFibre_over :
    geometricFibreToLG K M hM ≫ projection K =
      pullback.snd (familyProjection K) (matrixPoint K M hM) := by
  have h := congrArg (fun a => a ≫ parameterProjection K)
    (pullback.condition (f := familyProjection K) (g := matrixPoint K M hM))
  simpa only [geometricFibreToLG,Category.assoc,← family_over K,
    SplitMatrixGrassmannian.fieldPoint_projection,Category.comp_id] using h

@[reassoc] theorem cutIsoFibre_hom_base :
    (cutIsoFibre K M hM).hom ≫
      pullback.snd (familyProjection K) (matrixPoint K M hM) =
        (sectionCut K M).hom ≫ projection K := by
  rw [← geometricFibre_over,← Category.assoc,cutIsoFibre_hom_toLG]

abbrev model : Scheme.{u} :=
  LagrangianFiveSectionModel.curve K (LagrangianFibreFiveSection.fiveSection K M hM)

abbrev modelInclusion : model K M hM ⟶ space K :=
  LagrangianFiveSectionModel.inclusion K (LagrangianFibreFiveSection.fiveSection K M hM)

abbrev modelProjection : model K M hM ⟶ Spec (.of K) :=
  LagrangianFiveSectionModel.structureMap K (LagrangianFibreFiveSection.fiveSection K M hM)

def modelIsoFibre : model K M hM ≅ geometricFibre K M hM :=
  LagrangianFibreFiveSection.fiveSectionIsoFibre K M hM ≪≫
    pullbackSymmetry (matrixPoint K M hM) (familyProjection K)

omit [CharZero K] in
@[reassoc] theorem modelIsoFibre_hom_toLG :
    (modelIsoFibre K M hM).hom ≫ geometricFibreToLG K M hM = modelInclusion K M hM := by
  simp only [modelIsoFibre,Iso.trans_hom,geometricFibreToLG,Category.assoc,
    pullbackSymmetry_hom_comp_fst_assoc]
  exact LagrangianFibreFiveSection.fiveSectionIsoFibre_hom_toLG K M hM

/-- Exact comparison with the five-section bundle model used by
conormal and determinant calculations. -/
def cutIsoModel : (sectionCut K M).left ≅ model K M hM :=
  cutIsoFibre K M hM ≪≫ (modelIsoFibre K M hM).symm

@[reassoc] theorem cutIsoModel_hom_toLG :
    (cutIsoModel K M hM).hom ≫ modelInclusion K M hM = (sectionCut K M).hom := by
  rw [cutIsoModel,Iso.trans_hom,Iso.symm_hom,Category.assoc,← modelIsoFibre_hom_toLG,
    Iso.inv_hom_id_assoc]
  exact cutIsoFibre_hom_toLG K M hM

@[reassoc] theorem cutIsoModel_hom_base :
    (cutIsoModel K M hM).hom ≫ modelProjection K M hM =
      (sectionCut K M).hom ≫ projection K := by
  change (cutIsoModel K M hM).hom ≫ (modelInclusion K M hM ≫ projection K) = _
  rw [← Category.assoc,cutIsoModel_hom_toLG]

end M9Native.LagrangianOrderedFibre
end
