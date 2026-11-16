module

public import M9StacksIntegration.MukaiGenusNineSubobjects
public import M9StacksIntegration.MukaiImageCastelnuovo
public import M9StacksIntegration.MukaiRankTwoPreimageQuotient
public import M9StacksIntegration.MukaiSaturationGenericRank

/-!
# No saturated pencil line in the original nonsplit genus-nine extension

An original pencil line in E has exactly two sections. Its original
rank-two quotient has determinant degree at most ten. The actual H0
image has dimension at least four, so the proved native Castelnuovo
selection constructs a saturated line with two original lifting
sections. Its genuine pullback to E then has four sections and rank
two, contradicting the proved genus-nine subobject bound. Every
preimage, quotient map, and section is the original native object.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.MukaiNoPencilSubobject

variable (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
variable (hdim : topologicalKrullDim X ≤ 1)
variable (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
variable (S : ShortComplex X.Modules) (hS : S.ShortExact)
variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 S.X₁]
variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 S.X₃]
variable [FiniteDimensional k (cohomologyOverField k f S.X₁ 0)]
variable (hgen : MukaiSemiIrreducible.GloballyGenerated S.X₂)
variable (hA : invertibleCurveDegree k f hdim S.X₁ = 2)
variable (hB : invertibleCurveDegree k f hdim S.X₃ = 6)
variable (E α : X.Modules)
variable [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 α]
variable (i : S.X₂ ⟶ E) (p : E ⟶ α) (w : i ≫ p = 0)
variable (hT : (ShortComplex.mk i p w).ShortExact)
variable (hnonsplit : ∀ t : α ⟶ E, t ≫ p ≠ 𝟙 _)
variable (hα : invertibleCurveDegree k f hdim α = 8)
variable (hn : ¬ Nonempty (LinearSeries k f hdim 7 2))
variable (hEgen : MukaiSemiIrreducible.GloballyGenerated E)
variable (β : X.Modules)
variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
variable (hβ : invertibleCurveDegree k f hdim β = 8)
variable (e : MukaiBundleDeterminant.tensor α β ≅ Stacks.Duality.dualizingSheafOverField f)
variable (hg : genus f = 9)

include hnp hS hgen hA hB hT hnonsplit hα hn hEgen hβ e hg

/-- An actual saturated invertible subobject of E with a rank-two
bundle quotient cannot possess two independent global sections. -/
theorem impossible_of_two_sections
    (hreg : IsRegular X) (hdegree : curveDegree k f hdim E 3 = 16)
    (h6 : Module.finrank k (cohomologyOverField k f E 0) = 6)
    (η G : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 η]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G 2]
    (u : η ⟶ E) (v : E ⟶ G) (wv : u ≫ v = 0)
    (hU : (ShortComplex.mk u v wv).ShortExact)
    (hη : 2 ≤ Module.finrank k (cohomologyOverField k f η 0)) : False := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 3
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} G :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree G 2
  let : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X E
  let : G.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X G
  let : FiniteDimensional k (cohomologyOverField k f E 0) :=
    finiteDimensional_cohomologyOverField_of_isProper k f E 0
  let : FiniteDimensional k (cohomologyOverField k f G 0) :=
    finiteDimensional_cohomologyOverField_of_isProper k f G 0
  let : FiniteDimensional k (cohomologyOverField k f η 0) :=
    CurveDivisorSections.invertible_cohomology_zero_finite f η
  let : Mono u := hU.mono_f
  have hu : u ≠ 0 :=
    MukaiRankTwoSubobjectBound.hom_ne_zero_of_mono_of_h0_pos k f u (by omega)
  have hηtwo := MukaiExtensionLineBounds.h0_eq_two_of_nonzero_line_map
    k f hdim hnp S hS hgen hA hB E α i p w hT hnonsplit hα hn η hη u hu
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} η 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X η
  have hηdegree := MukaiPencilDegreeBounds.six_le_degree_of_two_sections f hdim hnp η hη
  have hdeg := curveDegree_add_of_shortExact_of_isProper k f hdim
    (ShortComplex.mk u v wv) hU 1 3 2
  rw [← invertibleCurveDegree_eq_curveDegree k f hdim η] at hdeg
  change curveDegree k f hdim E 3 = invertibleCurveDegree k f hdim η +
    curveDegree k f hdim G 2 at hdeg
  rw [hdegree] at hdeg
  have hGdegree : curveDegree k f hdim G 2 ≤ 10 := by omega
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Scheme.Modules.exteriorPower G 2) := MukaiTwistBounds.exterior_two_isInvertible G
  let : FiniteDimensional k
      (cohomologyOverField k f (Scheme.Modules.exteriorPower G 2) 0) :=
    CurveDivisorSections.invertible_cohomology_zero_finite f _
  have hdetdegree := MukaiTwistBounds.degree_exterior_two f G
  change invertibleCurveDegree k f hdim (Scheme.Modules.exteriorPower G 2) =
    curveDegree k f hdim G 2 at hdetdegree
  have hdet := MukaiResidualLineBounds.h0_le_four_of_degree_le_ten
    f hdim hg hnp α β e hα hβ (Scheme.Modules.exteriorPower G 2)
    (by rw [hdetdegree]; exact hGdegree)
  let U := ShortComplex.mk u v wv
  obtain ⟨L,N,j,q,wL,t,hL,hN,hLine,ht,hlift⟩ :=
    MukaiImageCastelnuovo.exists_line_with_lifting_sections k f U hU hreg hdim h6
      hηtwo.le hdet
  let := hL
  let := hN
  let : Mono j := hLine.mono_f
  obtain ⟨s,hs⟩ := exists_linearIndependent_of_le_finrank hη
  have hP := MukaiRankTwoPreimage.rank_two_with_four_sections f U hU j s hs t ht hlift
  let P := MukaiRankTwoPreimage.preimage U j
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} P 2 := hP.1
  have hSeq := MukaiRankTwoPreimageQuotient.quotientSequence_shortExact U j q wL hU hLine
  have hbound := MukaiGenusNineSubobjects.h0_le_three_of_subobject
    k f hdim hnp S hS hgen hA hB E α i p w hT hnonsplit hα hn hEgen β hβ e hg
    hreg hdegree P N (MukaiRankTwoPreimage.inclusion U j) (U.g ≫ q)
    (MukaiRankTwoPreimageQuotient.inclusion_comp_eq_zero U j q wL) hSeq
  have hfour : 4 ≤ Module.finrank k (cohomologyOverField k f P 0) := hP.2
  omega

/-- The original native exterior evaluation of every independent pair
is nonzero. Its hypothetical zero would construct an actual saturated
pencil line with the derived rank-two quotient just excluded above. -/
theorem lambda_two_ne_zero_of_independent_pair
    (hreg : IsRegular X) (hdegree : curveDegree k f hdim E 3 = 16)
    (h6 : Module.finrank k (cohomologyOverField k f E 0) = 6)
    (s : Fin 2 → cohomologyOverField k f E 0) (hs : LinearIndependent k s) :
    ExteriorEvaluation.lambda k f E 2 (exteriorPower.ιMulti k 2 s) ≠ 0 := by
  intro hw
  let hEF : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 3
  let : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  let : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X E
  let : FiniteDimensional k (cohomologyOverField k f E 0) :=
    finiteDimensional_cohomologyOverField_of_isProper k f E 0
  let φ := MukaiSemiIrreducible.evaluation k f E s
  let : (cokernel φ).IsQuasicoherent :=
    MukaiSaturationSections.evaluation_cokernel_isQuasicoherent k f E s
  have hET : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree E :=
    (isTorsionFree_iff_isFiniteLocallyFree hreg hdim E).mpr hEF
  have hgr : MukaiEvaluationGenericRank.genericRank k f E s = 1 :=
    MukaiSaturationRank.finrank_evaluation_generic_eq_one k f E hET s (hs.ne_zero 0) hw
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (MukaiEvaluationSaturation.saturation φ) 1 :=
    MukaiSaturationGenericRank.saturation_rank_of_genericRank_eq k f E s hreg hdim 1 hgr
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (MukaiEvaluationSaturation.saturation φ) :=
    Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace _
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (MukaiEvaluationSaturation.torsionFreeQuotient φ) 2 :=
    MukaiSaturationGenericRank.quotient_rank_of_genericRank_eq k f E s hreg hdim 3 1 hgr
  exact impossible_of_two_sections
    k f hdim hnp S hS hgen hA hB E α i p w hT hnonsplit hα hn hEgen β hβ e hg
    hreg hdegree h6 (MukaiEvaluationSaturation.saturation φ)
    (MukaiEvaluationSaturation.torsionFreeQuotient φ)
    (MukaiEvaluationSaturation.inclusion φ) (MukaiEvaluationSaturation.projection φ)
    (kernel.condition _) (MukaiEvaluationSaturation.sequence_shortExact φ)
    (MukaiSaturationSections.evaluation_saturation_h0_lower_bound k f E s hs)

end M9Native.MukaiNoPencilSubobject
