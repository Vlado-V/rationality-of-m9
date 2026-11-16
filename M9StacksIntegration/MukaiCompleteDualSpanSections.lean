module

public import M9StacksIntegration.MukaiDualSpanCurveDegree
public import M9StacksIntegration.MukaiFourSectionObstruction
public import M9StacksIntegration.MukaiDualSpanNoUnit
public import M9StacksIntegration.MukaiDualSpanDual

/-!
# Three sections of the actual complete dual span

The determinant is the original net line, whose three sections come
from its actual basis. Four sections of Q would produce an actual
two-pencil line filtration of total degree at least twelve, whereas
the constructed Q has degree eight. No canonical-bundle theorem or
genus hypothesis is required for this argument.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory
open M9Native.MukaiBundle M9Native.MukaiDualSpanDual

universe u

namespace M9Native.MukaiDualSpanSections

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]

theorem completeDualSpan_h0_eq_three
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (alpha : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property alpha]
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f alpha 0))
    (hgen : Epi (netEvaluation alpha (completeNetSections f alpha b)))
    (hdegree : invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le alpha = 8) :
    Module.finrank k (cohomologyOverField k f
      (dualSpan alpha (completeNetSections f alpha b)) 0) = 3 := by
  letI := isIso_globalSections_of_isAlgClosed k f
  let Q := dualSpan alpha (completeNetSections f alpha b)
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 2 :=
    dualSpan_rank alpha (completeNetSections f alpha b) hgen
  have hdeg : curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le Q 2 = 8 :=
    MukaiDualSpanDeterminant.dualSpan_curveDegree_eight k f
      (IsCurve.topologicalKrullDim_eq_one f).le alpha (completeNetSections f alpha b)
        hgen hdegree
  have hα : Module.finrank k (cohomologyOverField k f alpha 0) = 3 := by
    simpa using Module.finrank_eq_card_basis b
  have hdet : Module.finrank k (cohomologyOverField k f
      (Scheme.Modules.exteriorPower Q 2) 0) = 3 :=
    (cohomologyOverFieldIso k f
      (MukaiDualSpanDeterminant.dualSpanTopExteriorIso alpha
        (completeNetSections f alpha b) hgen) 0).toLinearEquiv.finrank_eq.trans hα
  have hgenerated := MukaiSemiIrreducible.dualSpan_globallyGenerated alpha
    (completeNetSections f alpha b) hgen
  have hvan := hom_structure_subsingleton_of_complete_net f alpha b hgen
  have hupper : Module.finrank k (cohomologyOverField k f Q 0) ≤ 3 := by
    by_contra h
    exact MukaiFourSectionObstruction.impossible f Q hnp (by omega) hgenerated
      (fun v => hvan.elim _ _) (by omega) (by omega)
  have hlower := three_le_dualSpan_cohomology_zero_finrank f
    (IsCurve.topologicalKrullDim_eq_one f).le alpha b
      (completeNetSections f alpha b) hgen (by omega)
  exact le_antisymm hupper hlower

end M9Native.MukaiDualSpanSections
