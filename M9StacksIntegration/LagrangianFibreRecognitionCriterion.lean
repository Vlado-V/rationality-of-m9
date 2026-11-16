module

public import M9StacksIntegration.LagrangianFibreConormalMap
public import M9StacksIntegration.SectionZeroRelativeConormal
public import M9StacksIntegration.ZeroConormalOpenImmersion
public import M9StacksIntegration.LagrangianIncidenceConnected

/-!
# Recognition of the whole original fibre after actual conormal generation

This downstream criterion takes invertibility of the actual original
row-to-conormal map as an explicit intermediate input. Its geometric
producer is separate. The full native section zero scheme then has zero
relative conormal along the actual curve. Local finite presentation comes
from the genuine finite-type ambient LG, while connectedness comes from
the proved unrestricted original family. Thus the original closed fibre
lift is an isomorphism, without assuming smoothness of that whole fibre.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace M9Native.LagrangianFibreRecognitionCriterion

open LagrangianGrassmannian LagrangianFiveSectionModel

variable (K : Type u) [Field K] [CharZero K] [IsAlgClosed K]
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)

/-- Connectedness concerns the actual full model and follows from the
proved connectedness of the unrestricted original incidence fibre. -/
theorem model_connected :
    ConnectedSpace (curve K (LagrangianFibreFiveSection.fiveSection K M hM)) := by
  let p := LagrangianMatrixPointRows.matrixPoint K M hM
  letI := LagrangianIncidenceConnected.baseChange_connected K K p
  letI : ConnectedSpace (LagrangianFibreFactorization.fibre K p) :=
    (Scheme.homeoOfIso (pullbackSymmetry p (LagrangianLinearSections.familyProjection K))).connectedSpace_iff.mpr
      inferInstance
  exact (Scheme.homeoOfIso (LagrangianFibreFiveSection.fiveSectionIsoFibre K M hM)).connectedSpace_iff.mpr
    inferInstance

omit [CharZero K] [IsAlgClosed K] in
/-- Finite type over the original field gives local Noetherianity;
no smoothness or regularity of the section zero scheme is used. -/
theorem model_locallyNoetherian :
    IsLocallyNoetherian (curve K (LagrangianFibreFiveSection.fiveSection K M hM)) := by
  letI : IsLocallyNoetherian (space K) :=
    LocallyOfFiniteType.isLocallyNoetherian (projection K)
  exact LocallyOfFiniteType.isLocallyNoetherian
    (inclusion K (LagrangianFibreFiveSection.fiveSection K M hM))

variable {X : Scheme.{u}}
  (i : X ⟶ space K) [IsClosedImmersion i]
  (q : X ⟶ LagrangianFibreFactorization.fibre K
    (LagrangianMatrixPointRows.matrixPoint K M hM))
  (hq : q ≫ LagrangianFibreFactorization.fibreToLG K
    (LagrangianMatrixPointRows.matrixPoint K M hM) = i)

/-- The literal comparison changes only the original zero-scheme
presentation and retains the original morphism to LG. -/
def modelLift : X ⟶ curve K (LagrangianFibreFiveSection.fiveSection K M hM) :=
  q ≫ (LagrangianFibreFiveSection.fiveSectionIsoFibre K M hM).inv

include hq in
theorem modelLift_toLG :
    modelLift K M hM q ≫
      inclusion K (LagrangianFibreFiveSection.fiveSection K M hM) = i := by
  let e := LagrangianFibreFiveSection.fiveSectionIsoFibre K M hM
  have he : e.inv ≫ inclusion K (LagrangianFibreFiveSection.fiveSection K M hM) =
      LagrangianFibreFactorization.fibreToLG K
        (LagrangianMatrixPointRows.matrixPoint K M hM) := by
    apply (cancel_epi e.hom).mp
    simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using
      (LagrangianFibreFiveSection.fiveSectionIsoFibre_hom_toLG K M hM).symm
  change (q ≫ e.inv) ≫ inclusion K (LagrangianFibreFiveSection.fiveSection K M hM) = i
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun a => q ≫ a) he).trans hq)

/-- This is an explicit intermediate criterion: the separate genuine
point/determinant proof must establish invertibility of the original
row map. Every subsequent whole-fibre hypothesis is derived here. -/
theorem isIso_fibreLift_of_isIso_sequenceMap [IsClosedImmersion q] [Nonempty X]
    [IsIso (LagrangianFibreConormalMap.sequenceMap K M hM i q hq)] : IsIso q := by
  let s := LagrangianFibreFiveSection.fiveSection K M hM
  let e := LagrangianFibreFiveSection.fiveSectionIsoFibre K M hM
  let q₀ := modelLift K M hM q
  letI : IsClosedImmersion q₀ := inferInstanceAs (IsClosedImmersion (q ≫ e.inv))
  letI := model_locallyNoetherian K M hM
  letI : LocallyOfFinitePresentation q₀ := inferInstance
  letI := model_connected K M hM
  have hs : pullbackGlobalSections i (LagrangianFiveSectionModel.equationBundle K) s = 0 :=
    LagrangianFibreConormalMap.pullback_fiveSection_eq_zero K M hM i q hq
  letI : IsIso (VanishingSectionConormalMap.conormalMap i
      (LagrangianFiveSectionModel.equationBundle K) s hs) := by
    apply (isIso_comp_right_iff _
      (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv).mp
    change IsIso (LagrangianFibreConormalMap.sequenceMap K M hM i q hq)
    infer_instance
  have hz : IsZero (Stacks.Conormal.conormalSheaf q₀) :=
    SectionZeroRelativeConormal.fullZero_isZero_conormalSheaf_of_triangle
      (LagrangianFiveSectionModel.equationBundle K) s i q₀ (modelLift_toLG K M hM i q hq) hs
  letI : IsIso q₀ := ZeroConormalOpenImmersion.isIso_of_isZero_conormal q₀ hz
  have heq : q₀ ≫ e.hom = q := by
    change (q ≫ e.inv) ≫ e.hom = q
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun a => q ≫ a) e.inv_hom_id).trans (Category.comp_id q))
  rw [← heq]
  infer_instance

end M9Native.LagrangianFibreRecognitionCriterion
