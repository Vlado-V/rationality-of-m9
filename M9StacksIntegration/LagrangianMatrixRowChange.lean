module

public import M9StacksIntegration.LineSectionRowChange
public import M9StacksIntegration.LagrangianOrderedFibre
public import M9StacksIntegration.LagrangianTripleFirstEquation

/-!
# The original five Lagrangian equations under an actual invertible row change

The literal fourteen coefficients, original structural scalar map and
original determinant sections are retained. All ideal equalities and
curve isomorphisms are over the original native LG, with full scheme
structure, and are proved from the actual inverse row action.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe u

namespace M9Native.LagrangianMatrixRowChange
open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianHyperplaneCoordinates
open LagrangianOrderedFibre LagrangianPrimitiveSystem
variable (K : Type u) [Field K] [CharZero K]

omit [CharZero K] in
/-- The changed matrix gives precisely the genuine row action on the
original determinant sections of the same original line. -/
theorem determinantSection_mul (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (M : Matrix (Fin 5) (Fin 14) K) (i : Fin 5) :
    determinantSection K ((A.val * M) i) =
      LineSectionRowChange.rowChange (coefficientMap K) A
        (fun j => determinantSection K (M j)) i := by
  simp only [determinantSection, LineSectionRowChange.rowChange, Matrix.mul_apply,
    map_sum, map_mul, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

omit [CharZero K] in
theorem equationIdeal_eq (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (M : Matrix (Fin 5) (Fin 14) K) :
    LineSectionIdealSum.ideal (determinantLine K) (sectionList K M) =
      LineSectionIdealSum.ideal (determinantLine K) (sectionList K (A.val * M)) := by
  change LineSectionRowChange.tupleIdeal (determinantLine K) (fun j => determinantSection K (M j)) =
    LineSectionRowChange.tupleIdeal (determinantLine K) (fun j => determinantSection K ((A.val * M) j))
  have hs : (fun j => determinantSection K ((A.val * M) j)) =
      LineSectionRowChange.rowChange (coefficientMap K) A (fun j => determinantSection K (M j)) :=
    funext (determinantSection_mul K A M)
  rw [hs]
  exact LineSectionRowChange.tupleIdeal_eq (coefficientMap K) (determinantLine K) A _

/-- The exact original five ordered cut models agree over the original LG. -/
def cutIso (A : Matrix.GeneralLinearGroup (Fin 5) K) (M : Matrix (Fin 5) (Fin 14) K) :
    (sectionCut K M).left ≅ (sectionCut K (A.val * M)).left :=
  LineSectionIdealSum.cutIso (determinantLine K) (sectionList K M) ≪≫
    eqToIso (congrArg (fun I : (space K).IdealSheafData => I.subscheme) (equationIdeal_eq K A M)) ≪≫
      (LineSectionIdealSum.cutIso (determinantLine K) (sectionList K (A.val * M))).symm

@[reassoc]
theorem cutIso_hom_toLG (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (M : Matrix (Fin 5) (Fin 14) K) :
    (cutIso K A M).hom ≫ (sectionCut K (A.val * M)).hom = (sectionCut K M).hom := by
  change (cutIso K A M).hom ≫
    (IteratedLineSectionCuts.simultaneousCut (determinantLine K) (sectionList K (A.val * M))).hom =
    (IteratedLineSectionCuts.simultaneousCut (determinantLine K) (sectionList K M)).hom
  simp only [cutIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    LineSectionIdealSum.cutIso_inv_comp]
  rw [LagrangianMatrixChart.eqToIso_subscheme_ι _ _ (equationIdeal_eq K A M),
    LineSectionIdealSum.cutIso_hom_comp]

/-- The actual original five-section model has exactly the full sum
of the original five determinant-section ideals. -/
theorem modelInclusion_ker (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec) :
    (modelInclusion K M hM).ker =
      LineSectionIdealSum.ideal (determinantLine K) (sectionList K M) := by
  have h := congrArg Scheme.Hom.ker (cutIsoModel_hom_toLG K M hM)
  rw [Scheme.Hom.ker_comp_of_isIso] at h
  exact h.trans (LineSectionIdealSum.cut_ker (determinantLine K) (sectionList K M))

end M9Native.LagrangianMatrixRowChange
