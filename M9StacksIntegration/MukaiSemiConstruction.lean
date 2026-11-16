module

public import M9StacksIntegration.MukaiOriginalImageBounds
public import M9StacksIntegration.MukaiImageComparison
public import M9StacksIntegration.MukaiShortExactFiberRank
public import M9StacksIntegration.MukaiNoDegreeSevenNet

/-!
# Actual semi-irreducibility of the original nonsplit extension

The literal original evaluation image and its independently constructed
saturation have derived rank two and opposite degree bounds. Actual
monomorphism degree comparison makes their canonical comparison an
isomorphism. The original three-generator evaluation is therefore
epimorphic onto that actual subbundle, and actual residue-fibre
right-exactness gives rank two everywhere. The complete native
semi-irreducibility predicate follows without a semi-irreducibility,
image-saturation equality, or determinant-section premise.

The final filtration theorem derives the degree sixteen and absence
of a degree-seven net. Its original degree-two/degree-six filtration
is the actual sheaf sequence constructed by the native pencil geometry.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.MukaiSemiConstruction

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
variable [FiniteDimensional k (cohomologyOverField k f E 0)]
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

/-- The canonical original-image-to-saturation map is proved to be
an actual isomorphism, using the two independently established degrees. -/
theorem imageToSaturation_isIso
    (hreg : IsRegular X) (hdegree : curveDegree k f hdim E 3 = 16)
    (h6 : Module.finrank k (cohomologyOverField k f E 0) = 6)
    (s : Fin 3 → cohomologyOverField k f E 0) (hs : LinearIndependent k s)
    (hnmono : ¬ Mono (MukaiSemiIrreducible.evaluation k f E s)) :
    letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 3
    letI : E.IsQuasicoherent :=
      Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
    letI : (cokernel (MukaiSemiIrreducible.evaluation k f E s)).IsQuasicoherent :=
      MukaiSaturationSections.evaluation_cokernel_isQuasicoherent k f E s
    IsIso (MukaiEvaluationImage.imageToSaturation (MukaiSemiIrreducible.evaluation k f E s)) := by
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 3
  let : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  let φ := MukaiSemiIrreducible.evaluation k f E s
  let : (cokernel φ).IsQuasicoherent :=
    MukaiSaturationSections.evaluation_cokernel_isQuasicoherent k f E s
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (MukaiEvaluationImage.evaluationImage k f E s) 2 :=
    MukaiOriginalImageBounds.originalImage_rank_two
      k f hdim hnp S hS hgen hA hB E α i p w hT hnonsplit hα hn hreg s hs hnmono
  obtain ⟨hF,hξ,hSeq,h0F⟩ := MukaiTripleSaturation.triple_saturation_line_quotient
    k f hdim hnp S hS hgen hA hB E α i p w hT hnonsplit hα hn hreg s hs hnmono
  let := hF
  have hd := MukaiOriginalImageBounds.degree_bounds
    k f hdim hnp S hS hgen hA hB E α i p w hT hnonsplit hα hn hEgen β hβ e hg
    hreg hdegree h6 s hs hnmono
  exact MukaiImageComparison.isIso_of_target_degree_le_source f hdim
    (MukaiEvaluationImage.imageToSaturation φ) (hd.2.trans hd.1)

/-- The original complete native system is semi-irreducible: every
independent triple is actually monic or has actual fibre rank two everywhere. -/
theorem completeSemiIrreducible
    (hdegree : curveDegree k f hdim E 3 = 16)
    (h6 : Module.finrank k (cohomologyOverField k f E 0) = 6) :
    MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3 := by
  have hreg : IsRegular X := isRegular_of_smooth_over_field f
  intro s hs
  by_cases hm : Mono (MukaiSemiIrreducible.evaluation k f E s)
  · exact Or.inl hm
  · apply Or.inr
    let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 3
    let : E.IsQuasicoherent :=
      Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
    let φ := MukaiSemiIrreducible.evaluation k f E s
    let : (cokernel φ).IsQuasicoherent :=
      MukaiSaturationSections.evaluation_cokernel_isQuasicoherent k f E s
    obtain ⟨hF,hξ,hSeq,h0F⟩ := MukaiTripleSaturation.triple_saturation_line_quotient
      k f hdim hnp S hS hgen hA hB E α i p w hT hnonsplit hα hn hreg s hs hm
    let := hξ
    let : IsIso (MukaiEvaluationImage.imageToSaturation φ) :=
      imageToSaturation_isIso
        k f hdim hnp S hS hgen hA hB E α i p w hT hnonsplit hα hn hEgen β hβ e hg
        hreg hdegree h6 s hs hm
    let δ : _root_.SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 3)) ⟶
        MukaiEvaluationSaturation.saturation φ :=
      factorThruImage φ ≫ MukaiEvaluationImage.imageToSaturation φ
    let : Epi δ := by dsimp [δ]; infer_instance
    let SatSeq := ShortComplex.mk (MukaiEvaluationSaturation.inclusion φ)
      (MukaiEvaluationSaturation.projection φ) (kernel.condition _)
    have hSatSeq : SatSeq.ShortExact := hSeq
    have hr := MukaiShortExactFiberRank.everywhereRank_freeThree_comp_inclusion SatSeq hSatSeq δ
    have hfac : δ ≫ SatSeq.f = φ := by
      change (factorThruImage φ ≫ MukaiEvaluationImage.imageToSaturation φ) ≫
        MukaiEvaluationSaturation.inclusion φ = φ
      rw [Category.assoc,MukaiEvaluationImage.imageToSaturation_inclusion,image.fac]
    rw [hfac] at hr
    exact hr

omit hn in
/-- The actual no-degree-five-pencil condition supplies the missing
degree-seven-net exclusion, and the two original exact filtrations
derive degree sixteen. No semi-irreducibility, determinant-section, or
image-saturation premise appears. -/
theorem completeSemiIrreducible_of_no_pencil
    (h6 : Module.finrank k (cohomologyOverField k f E 0) = 6) :
    MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3 := by
  have h7 : ¬ Nonempty (LinearSeries k f hdim 7 2) :=
    MukaiNoDegreeSevenNet.no_net_of_degree_le_seven f hdim hg hnp 7 (by decide)
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₁ 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X S.X₁
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₃ 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X S.X₃
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₂ 2 :=
    MukaiBundle.extension_rank S hS 1 1 inferInstance inferInstance
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} α 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X α
  have hQ := curveDegree_add_of_shortExact_of_isProper k f hdim S hS 1 2 1
  rw [← invertibleCurveDegree_eq_curveDegree k f hdim S.X₁,
    ← invertibleCurveDegree_eq_curveDegree k f hdim S.X₃] at hQ
  change curveDegree k f hdim S.X₂ 2 = invertibleCurveDegree k f hdim S.X₁ +
    invertibleCurveDegree k f hdim S.X₃ at hQ
  rw [hA,hB] at hQ
  have hdegree := curveDegree_add_of_shortExact_of_isProper k f hdim
    (ShortComplex.mk i p w) hT 2 3 1
  rw [← invertibleCurveDegree_eq_curveDegree k f hdim α] at hdegree
  change curveDegree k f hdim E 3 = curveDegree k f hdim S.X₂ 2 +
    invertibleCurveDegree k f hdim α at hdegree
  rw [hQ,hα] at hdegree
  norm_num at hdegree
  exact completeSemiIrreducible
    k f hdim hnp S hS hgen hA hB E α i p w hT hnonsplit hα h7 hEgen β hβ e hg hdegree h6

end M9Native.MukaiSemiConstruction
