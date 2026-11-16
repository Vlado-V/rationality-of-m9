module

public import M9StacksIntegration.MukaiLemmaFiveOne
public import M9StacksIntegration.MukaiBundleUniqueness

/-!
# The actual Hom vanishing used in residual-net extensions

The native finite locally free tensor-Hom isomorphism identifies the
actual Hom space with native H0 of the actual tensor with the dual.
Mukai Lemma 5.1 therefore gives Hom(alpha,Q_beta)=0 directly, without
an assumed vanishing of Hom or of an extension group.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundle M9Native.MukaiDualSpanSections

universe u

namespace M9Native.MukaiResidualHomVanishing

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k))

/-- The actual scalar-compatible Hom/H0 comparison for an invertible
source, using the genuine native dual-tensor-Hom isomorphism. -/
def homDualTensorH0Equiv (alpha Q : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property alpha] :
    letI := modulesLinearOverField k f
    (alpha ⟶ Q) ≃ₗ[k] cohomologyOverField k f
      (Scheme.Modules.tensorObj (dualSheaf alpha) Q) 0 := by
  letI := modulesLinearOverField k f
  letI := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X alpha
  exact (MukaiBundleUniqueness.homH0SheafHomLinearEquiv k f alpha Q).trans
    (cohomologyOverFieldIso k f
      (Stacks.SheafOfModules.Scheme.dualTensorIsoSheafHomOfRank alpha Q 1).symm 0).toLinearEquiv

/-- The actual complete dual span of any degree-eight net has no map
from any degree-eight line bundle on the original nonpentagonal curve. -/
theorem hom_completeDualSpan_subsingleton
    [IsAlgClosed k] [IsProper f] [IsCurve k f] [Smooth f]
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (Ebeta : LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 8 2)
    (bB : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f Ebeta.L 0))
    (alpha : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property alpha]
    (ha : invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le alpha = 8) :
    Subsingleton (alpha ⟶ dualSpan Ebeta.L (completeNetSections f Ebeta.L bB)) := by
  have hv := (MukaiLemmaFiveOne.lemma_five_one_for_complete_basis f
    (IsCurve.topologicalKrullDim_eq_one f).le hg hnp Ebeta bB alpha ha).2
  letI := hv
  exact (homDualTensorH0Equiv f alpha
    (dualSpan Ebeta.L (completeNetSections f Ebeta.L bB))).toEquiv.subsingleton

end M9Native.MukaiResidualHomVanishing
