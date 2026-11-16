module

public import M9StacksIntegration.MukaiNoPencilSubobject
public import M9StacksIntegration.MukaiTripleSaturation
public import M9StacksIntegration.MukaiEvaluationImage
public import M9StacksIntegration.MukaiEvaluationImageDegree

/-!
# Independent native degree bounds on the original image and saturation

The original nonmonic independent triple has genuine rank two, hence
both its categorical image and its prescribed saturation are actual
rank-two bundles. The actual ambient no-pencil theorem and genuine
three-dimensional exterior decomposition derive three determinant
sections for the original image, giving degree at least eight. The
actual rank-two subobject bound and native H0 exactness give three
sections of the saturation's line quotient, bounding the saturation's
degree by eight. The image is not identified with its saturation here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.MukaiOriginalImageBounds

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

include hnp hS hgen hA hB hT hnonsplit hα hn

/-- The literal original evaluation image has derived rank two. -/
theorem originalImage_rank_two
    (hreg : IsRegular X)
    (s : Fin 3 → cohomologyOverField k f E 0) (hs : LinearIndependent k s)
    (hnmono : ¬ Mono (MukaiSemiIrreducible.evaluation k f E s)) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (MukaiEvaluationImage.evaluationImage k f E s) 2 := by
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 3
  have hd := MukaiTripleSaturation.triple_genericRank_eq_two
    k f hdim hnp S hS hgen hA hB E α i p w hT hnonsplit hα hn hreg s hs hnmono
  exact MukaiEvaluationImage.evaluationImage_rank k f E s hreg hdim 2 hd

variable (hEgen : MukaiSemiIrreducible.GloballyGenerated E)
variable (β : X.Modules)
variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
variable (hβ : invertibleCurveDegree k f hdim β = 8)
variable (e : MukaiBundleDeterminant.tensor α β ≅ Stacks.Duality.dualizingSheafOverField f)
variable (hg : genus f = 9)

include hEgen hβ e hg

/-- The actual original image has degree at least eight and its
independently constructed actual saturation has degree at most eight.
Both rank instances are derived inside the statement and proof. -/
theorem degree_bounds
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
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
        (MukaiEvaluationImage.evaluationImage k f E s) 2 :=
      originalImage_rank_two k f hdim hnp S hS hgen hA hB E α i p w hT hnonsplit hα hn
        hreg s hs hnmono
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
        (MukaiEvaluationSaturation.saturation (MukaiSemiIrreducible.evaluation k f E s)) 2 :=
      (MukaiTripleSaturation.triple_saturation_line_quotient
        k f hdim hnp S hS hgen hA hB E α i p w hT hnonsplit hα hn hreg s hs hnmono).1
    (8 : ℤ) ≤ curveDegree k f hdim (MukaiEvaluationImage.evaluationImage k f E s) 2 ∧
      curveDegree k f hdim
        (MukaiEvaluationSaturation.saturation (MukaiSemiIrreducible.evaluation k f E s)) 2 ≤ 8 := by
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 3
  let : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  let φ := MukaiSemiIrreducible.evaluation k f E s
  let : (cokernel φ).IsQuasicoherent :=
    MukaiSaturationSections.evaluation_cokernel_isQuasicoherent k f E s
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (MukaiEvaluationImage.evaluationImage k f E s) 2 :=
    originalImage_rank_two k f hdim hnp S hS hgen hA hB E α i p w hT hnonsplit hα hn
      hreg s hs hnmono
  obtain ⟨hF,hξ,hSeq,h0F⟩ := MukaiTripleSaturation.triple_saturation_line_quotient
    k f hdim hnp S hS hgen hA hB E α i p w hT hnonsplit hα hn hreg s hs hnmono
  let := hF
  let := hξ
  let : FiniteDimensional k
      (cohomologyOverField k f (MukaiEvaluationSaturation.saturation φ) 0) :=
    MukaiSaturationSections.finite_h0_saturation k f φ
  have hpair := MukaiNoPencilSubobject.lambda_two_ne_zero_of_independent_pair
    k f hdim hnp S hS hgen hA hB E α i p w hT hnonsplit hα hn hEgen β hβ e hg
    hreg hdegree h6
  have hlow := MukaiEvaluationImageDegree.eight_le_degree_of_three_sections_and_mono
    k f hdim hn (MukaiEvaluationImage.evaluationImage k f E s) E (image.ι φ)
    (MukaiEvaluationImage.evaluationImage_h0_lower_bound k f E s hs) hpair
  have hFbound := MukaiGenusNineSubobjects.h0_le_three_of_subobject
    k f hdim hnp S hS hgen hA hB E α i p w hT hnonsplit hα hn hEgen β hβ e hg
    hreg hdegree (MukaiEvaluationSaturation.saturation φ)
    (MukaiEvaluationSaturation.torsionFreeQuotient φ)
    (MukaiEvaluationSaturation.inclusion φ) (MukaiEvaluationSaturation.projection φ)
    (kernel.condition _) hSeq
  have hhigh := MukaiEvaluationImageDegree.degree_le_eight_of_line_quotient
    k f hdim hn (MukaiEvaluationSaturation.saturation φ) E
    (MukaiEvaluationSaturation.torsionFreeQuotient φ)
    (MukaiEvaluationSaturation.inclusion φ) (MukaiEvaluationSaturation.projection φ)
    (kernel.condition _) hSeq h6 hFbound hdegree
  exact ⟨hlow,hhigh⟩

end M9Native.MukaiOriginalImageBounds
