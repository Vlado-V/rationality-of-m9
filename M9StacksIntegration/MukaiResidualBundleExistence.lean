module

public import M9StacksIntegration.MukaiCompleteNetHomBasis
public import M9StacksIntegration.MukaiResidualHomVanishing
public import M9StacksIntegration.MukaiDualSpanAnnihilatorDeterminant
public import M9StacksIntegration.MukaiDualSpanCurveDegree
public import M9StacksIntegration.MukaiRankTwoParity
public import M9StacksIntegration.MukaiDualSpanSemiIrreducible

/-!
# Existence of the actual residual-net Mukai bundle

The determinant and degree of the two actual dual spans supply the
geometric rank-two parity theorem. The genuine extension kernel then
contains a nonzero class, which produces the actual nonsplit extension.
The complete section basis supplies Gamma-splitting, and the checked
Proposition 5.3 gives global generation and complete semi-irreducibility.

The inputs are the two original degree-eight nets and their actual
residual isomorphism. No extension, parity, rank, section count,
generation, or semi-irreducibility conclusion is assumed. The existence
of the original degree-eight net is the separate Brill--Noether theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open M9Native.MukaiBundle M9Native.MukaiBundleDeterminant
open M9Native.MukaiDualSpanSections

universe u

namespace M9Native.MukaiResidualBundleExistence

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]

local instance nativeHasExt : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules

/-- Mukai Lemma 5.2 for the original complete residual nets: parity,
the nonzero extension class, the nonsplit extension, and its six actual
sections are all derived from the actual geometric data. -/
theorem exists_nonsplit_gammaSplit_complete_nets
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (A B : LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 8 2)
    (bA : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f A.L 0))
    (bB : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f B.L 0))
    (hres : tensor A.L B.L ≅ Stacks.Duality.dualizingSheafOverField f) :
    ∃ (E : X.Modules)
      (i : dualSpan B.L (completeNetSections f B.L bB) ⟶ E)
      (p : E ⟶ A.L) (w : i ≫ p = 0)
      (h : (ShortComplex.mk i p w).ShortExact),
      h.extClass ≠ 0 ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3 ∧
      Function.Surjective (SheafOfModules.sectionsMap p) ∧
      ¬ Nonempty (ShortComplex.mk i p w).Splitting ∧
      Module.finrank k (cohomologyOverField k f E 0) = 6 := by
  let := A.isInvertible
  let := B.isInvertible
  let QA := dualSpan A.L (completeNetSections f A.L bA)
  let QB := dualSpan B.L (completeNetSections f B.L bB)
  have hno7 := MukaiNoDegreeSevenNet.no_net_of_degree_le_seven f
    (IsCurve.topologicalKrullDim_eq_one f).le hg hnp
  have hA := MukaiCompleteEvaluation.degree_eight_completeNetEvaluation_epi f
    (IsCurve.topologicalKrullDim_eq_one f).le hno7 A bA
  have hB := MukaiCompleteEvaluation.degree_eight_completeNetEvaluation_epi f
    (IsCurve.topologicalKrullDim_eq_one f).le hno7 B bB
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} QA 2 :=
    dualSpan_rank A.L (completeNetSections f A.L bA) hA
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} QB 2 :=
    dualSpan_rank B.L (completeNetSections f B.L bB) hB
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} A.L 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X A.L
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tensor QB QA) 4 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X QB QA 2 2
  let : QA.IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f QA 2
  let : QB.IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f QB 2
  let : A.L.IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f A.L 1
  let : (tensor QB QA).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f
      (tensor QB QA) 4
  let := finiteDimensional_cohomologyOverField_of_isProper k f QB 0
  let := finiteDimensional_cohomologyOverField_of_isProper k f A.L 0
  let := finiteDimensional_cohomologyOverField_of_isProper k f (tensor QB QA) 0
  have hQ := (MukaiLemmaFiveOne.lemma_five_one_for_complete_basis f
    (IsCurve.topologicalKrullDim_eq_one f).le hg hnp B bB A.L A.degree_eq).1
  have ha0 : Module.finrank k (cohomologyOverField k f A.L 0) = 3 := by
    simpa using Module.finrank_eq_card_basis bA
  have hvan := MukaiResidualHomVanishing.hom_completeDualSpan_subsingleton f
    hg hnp B bB A.L A.degree_eq
  have hspan := MukaiCompleteNetHomBasis.completeNetSections_hom_span f A.L bA
  let d : tensor (Scheme.Modules.determinant QB) (Scheme.Modules.determinant QA) ≅
      MukaiHomSerreTrace.curveDualizingModule k f :=
    MukaiDualSpanDeterminant.dualSpansDeterminantTensorIso B.L A.L
      (completeNetSections f B.L bB) hB (completeNetSections f A.L bA) hA ≪≫
    Stacks.SheafOfModules.Invertible.tensorProductBraiding
      X.presheaf X.ringCatSheaf.2 B.L A.L ≪≫ hres ≪≫
    (MukaiHomSerreTrace.curveDualizingModuleIso k f
      (IsCurve.topologicalKrullDim_eq_one f)).symm
  have hdeg := MukaiDualSpanDeterminant.dualSpan_curveDegree_eight k f
    (IsCurve.topologicalKrullDim_eq_one f).le B.L
    (completeNetSections f B.L bB) hB B.degree_eq
  have heven := MukaiRankTwoParity.even_H0_tensor_of_degree_eight k f QB QA
    inferInstance inferInstance d hdeg
  exact MukaiBundleUniqueness.exists_nonsplit_H0_six_of_even_tensor_H0 k f QB A.L
    inferInstance (completeNetSections f A.L bA) hA hQ ha0 hvan hspan heven

/-- The actual canonical, generated, complete semi-irreducible rank-three
bundle is constructed from the original residual nets. -/
theorem exists_canonical_generated_semiIrreducible_complete_nets
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (A B : LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 8 2)
    (bA : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f A.L 0))
    (bB : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f B.L 0))
    (hres : tensor A.L B.L ≅ Stacks.Duality.dualizingSheafOverField f) :
    ∃ E : X.Modules,
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3 ∧
      Module.finrank k (cohomologyOverField k f E 0) = 6 ∧
      Nonempty (Scheme.Modules.exteriorPower E 3 ≅ Stacks.Duality.dualizingSheafOverField f) ∧
      MukaiSemiIrreducible.GloballyGenerated E ∧
      MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3 := by
  let := A.isInvertible
  let := B.isInvertible
  obtain ⟨E, i, p, w, h, _, hr, hgamma, hn, h6⟩ :=
    exists_nonsplit_gammaSplit_complete_nets f hg hnp A B bA bB hres
  have hno7 := MukaiNoDegreeSevenNet.no_net_of_degree_le_seven f
    (IsCurve.topologicalKrullDim_eq_one f).le hg hnp
  have hB := MukaiCompleteEvaluation.degree_eight_completeNetEvaluation_epi f
    (IsCurve.topologicalKrullDim_eq_one f).le hno7 B bB
  let d : Scheme.Modules.exteriorPower E 3 ≅ Stacks.Duality.dualizingSheafOverField f :=
    MukaiDualSpanDeterminant.extensionTopExteriorIso B.L A.L
      (completeNetSections f B.L bB) hB i p w h ≪≫ hres
  have hnonsplit (t : A.L ⟶ E) : t ≫ p ≠ 𝟙 _ := by
    intro ht
    exact hn ⟨ShortComplex.Splitting.ofExactOfSection _ h.exact t ht h.mono_f⟩
  have hsemi := MukaiDualSpanSemiIrreducible.free_and_semiIrreducible_for_complete_basis f
    (IsCurve.topologicalKrullDim_eq_one f).le hg hnp A B bB hres E i p w h hnonsplit hgamma
  exact ⟨E, hr, h6, ⟨d⟩, hsemi.1, hsemi.2⟩

end M9Native.MukaiResidualBundleExistence
