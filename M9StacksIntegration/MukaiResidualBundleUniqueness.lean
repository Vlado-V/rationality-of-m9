module

public import M9StacksIntegration.MukaiTensorSectionBound
public import M9StacksIntegration.MukaiResidualHomVanishing
public import M9StacksIntegration.MukaiResidualExtensionSections

/-!
# Uniqueness of the actual residual-net extensions

The genuine tensor bound and Mukai Lemma 5.1 discharge the geometric
premises of the actual Ext classification. The result compares actual
middle sheaves of actual nonsplit extensions; no bundle class or
uniqueness predicate is introduced. Recognition of an arbitrary Mukai
bundle as such an extension is a separate geometric theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open M9Native.MukaiBundle M9Native.MukaiBundleDeterminant
open M9Native.MukaiDualSpanSections

universe u

namespace M9Native.MukaiResidualBundleUniqueness

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]

/-- All actual nonsplit Gamma-split extensions of these original
complete residual nets have isomorphic actual middle sheaves. -/
theorem gammaSplit_middle_iso_complete_nets
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (Ealpha Ebeta : LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 8 2)
    (bA : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f Ealpha.L 0))
    (bB : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f Ebeta.L 0))
    (hres : tensor Ealpha.L Ebeta.L ≅ Stacks.Duality.dualizingSheafOverField f)
    {E E' : X.Modules}
    {i : dualSpan Ebeta.L (completeNetSections f Ebeta.L bB) ⟶ E}
    {p : E ⟶ Ealpha.L} {z : i ≫ p = 0}
    {i' : dualSpan Ebeta.L (completeNetSections f Ebeta.L bB) ⟶ E'}
    {p' : E' ⟶ Ealpha.L} {z' : i' ≫ p' = 0}
    (h : (ShortComplex.mk i p z).ShortExact)
    (h' : (ShortComplex.mk i' p' z').ShortExact)
    (hgamma : Function.Surjective (SheafOfModules.sectionsMap p))
    (hgamma' : Function.Surjective (SheafOfModules.sectionsMap p'))
    (hn : ¬ Nonempty (ShortComplex.mk i p z).Splitting)
    (hn' : ¬ Nonempty (ShortComplex.mk i' p' z').Splitting) :
    Nonempty (E ≅ E') := by
  letI := Ealpha.isInvertible
  letI := Ebeta.isInvertible
  let A := dualSpan Ealpha.L (completeNetSections f Ealpha.L bA)
  let B := dualSpan Ebeta.L (completeNetSections f Ebeta.L bB)
  have hno7 := MukaiNoDegreeSevenNet.no_net_of_degree_le_seven f
    (IsCurve.topologicalKrullDim_eq_one f).le hg hnp
  have hA := MukaiCompleteEvaluation.degree_eight_completeNetEvaluation_epi f
    (IsCurve.topologicalKrullDim_eq_one f).le hno7 Ealpha bA
  have hB := MukaiCompleteEvaluation.degree_eight_completeNetEvaluation_epi f
    (IsCurve.topologicalKrullDim_eq_one f).le hno7 Ebeta bB
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} A 2 :=
    dualSpan_rank Ealpha.L (completeNetSections f Ealpha.L bA) hA
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} B 2 :=
    dualSpan_rank Ebeta.L (completeNetSections f Ebeta.L bB) hB
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tensor B A) 4 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X B A 2 2
  letI : B.IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f B 2
  letI : (tensor B A).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f
      (tensor B A) 4
  letI := finiteDimensional_cohomologyOverField_of_isProper k f B 0
  letI := finiteDimensional_cohomologyOverField_of_isProper k f (tensor B A) 0
  have hQ := (MukaiLemmaFiveOne.lemma_five_one_for_complete_basis f
    (IsCurve.topologicalKrullDim_eq_one f).le hg hnp Ebeta bB Ealpha.L Ealpha.degree_eq).1
  have hvan := MukaiResidualHomVanishing.hom_completeDualSpan_subsingleton f
    hg hnp Ebeta bB Ealpha.L Ealpha.degree_eq
  have hAB := MukaiTensorSectionBound.tensor_h0_le_ten_complete_nets f
    hg hnp Ealpha Ebeta bA bB hres
  have hcomm := (cohomologyOverFieldIso k f
    (MukaiTensorLineCancellation.tensorSwap B A) 0).toLinearEquiv.finrank_eq
  have h10 : Module.finrank k (cohomologyOverField k f (tensor B A) 0) ≤ 10 :=
    hcomm.trans_le hAB
  exact MukaiBundleUniqueness.gammaSplit_middle_iso_of_tensor_H0_bound k f
    (completeNetSections f Ealpha.L bA) hA hQ hvan h10 h h' hgamma hgamma' hn hn'

/-- Six or more actual sections force Gamma-splitting of these actual
extensions, so their nonsplit middle sheaves are unique up to iso.
The middle ranks and all H0 finiteness are derived from exactness. -/
theorem middle_iso_of_h0_ge_six_complete_nets
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (Ealpha Ebeta : LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 8 2)
    (bA : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f Ealpha.L 0))
    (bB : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f Ebeta.L 0))
    (hres : tensor Ealpha.L Ebeta.L ≅ Stacks.Duality.dualizingSheafOverField f)
    {E E' : X.Modules}
    {i : dualSpan Ebeta.L (completeNetSections f Ebeta.L bB) ⟶ E}
    {p : E ⟶ Ealpha.L} {z : i ≫ p = 0}
    {i' : dualSpan Ebeta.L (completeNetSections f Ebeta.L bB) ⟶ E'}
    {p' : E' ⟶ Ealpha.L} {z' : i' ≫ p' = 0}
    (h : (ShortComplex.mk i p z).ShortExact)
    (h' : (ShortComplex.mk i' p' z').ShortExact)
    (h6 : 6 ≤ Module.finrank k (cohomologyOverField k f E 0))
    (h6' : 6 ≤ Module.finrank k (cohomologyOverField k f E' 0))
    (hn : ¬ Nonempty (ShortComplex.mk i p z).Splitting)
    (hn' : ¬ Nonempty (ShortComplex.mk i' p' z').Splitting) :
    Nonempty (E ≅ E') := by
  exact gammaSplit_middle_iso_complete_nets f hg hnp Ealpha Ebeta bA bB hres h h'
    (gammaSplit_of_h0_ge_six_complete_nets f hg hnp Ealpha Ebeta bA bB h h6)
    (gammaSplit_of_h0_ge_six_complete_nets f hg hnp Ealpha Ebeta bA bB h' h6') hn hn'

end M9Native.MukaiResidualBundleUniqueness
