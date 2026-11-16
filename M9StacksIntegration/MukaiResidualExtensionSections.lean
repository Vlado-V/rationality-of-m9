module

public import M9StacksIntegration.MukaiResidualHomVanishing
public import M9StacksIntegration.MukaiTensorPencilBound

/-!
# Six sections force Gamma-splitting of actual residual-net extensions

The endpoint H0 dimensions come from the original complete bases and
the proved Mukai Lemma 5.1. The middle rank is derived from the actual
short exact sequence. Native cohomology then forces surjectivity on
the actual global sections; no Gamma-splitting premise is supplied.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open M9Native.MukaiBundle M9Native.MukaiDualSpanSections

universe u

namespace M9Native.MukaiResidualBundleUniqueness

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]

/-- The original section map of an actual extension is surjective
whenever its actual middle sheaf has at least six sections. -/
theorem gammaSplit_of_h0_ge_six_complete_nets
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (Ealpha Ebeta : LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 8 2)
    (bA : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f Ealpha.L 0))
    (bB : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f Ebeta.L 0))
    {E : X.Modules}
    {i : dualSpan Ebeta.L (completeNetSections f Ebeta.L bB) ⟶ E}
    {p : E ⟶ Ealpha.L} {z : i ≫ p = 0}
    (h : (ShortComplex.mk i p z).ShortExact)
    (h6 : 6 ≤ Module.finrank k (cohomologyOverField k f E 0)) :
    Function.Surjective (SheafOfModules.sectionsMap p) := by
  letI := Ealpha.isInvertible
  letI := Ebeta.isInvertible
  let B := dualSpan Ebeta.L (completeNetSections f Ebeta.L bB)
  have hno7 := MukaiNoDegreeSevenNet.no_net_of_degree_le_seven f
    (IsCurve.topologicalKrullDim_eq_one f).le hg hnp
  have hB := MukaiCompleteEvaluation.degree_eight_completeNetEvaluation_epi f
    (IsCurve.topologicalKrullDim_eq_one f).le hno7 Ebeta bB
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} B 2 :=
    dualSpan_rank Ebeta.L (completeNetSections f Ebeta.L bB) hB
  letI := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X Ealpha.L
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3 :=
    extension_rank (ShortComplex.mk i p z) h 2 1 inferInstance inferInstance
  letI : B.IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f B 2
  letI : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f E 3
  letI : Ealpha.L.IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f Ealpha.L 1
  letI := finiteDimensional_cohomologyOverField_of_isProper k f B 0
  letI := finiteDimensional_cohomologyOverField_of_isProper k f Ealpha.L 0
  letI := finiteDimensional_cohomologyOverField_of_isProper k f E 0
  have hQ := (MukaiLemmaFiveOne.lemma_five_one_for_complete_basis f
    (IsCurve.topologicalKrullDim_eq_one f).le hg hnp Ebeta bB Ealpha.L Ealpha.degree_eq).1
  change Module.finrank k (cohomologyOverField k f B 0) = 3 at hQ
  have ha0 : Module.finrank k (cohomologyOverField k f Ealpha.L 0) = 3 := by
    simpa using Module.finrank_eq_card_basis bA
  have hbnd := MukaiBundleUniqueness.finrank_H0_le_add k f h
  change Module.finrank k (cohomologyOverField k f E 0) ≤
    Module.finrank k (cohomologyOverField k f B 0) +
      Module.finrank k (cohomologyOverField k f Ealpha.L 0) at hbnd
  have hEq : Module.finrank k (cohomologyOverField k f E 0) = 6 := by omega
  exact (MukaiBundleUniqueness.gammaSplit_iff_H0_six k f h hQ ha0).2 hEq

end M9Native.MukaiResidualBundleUniqueness
