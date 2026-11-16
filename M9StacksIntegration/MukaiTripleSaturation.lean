module

public import M9StacksIntegration.MukaiExtensionLineBounds
public import M9StacksIntegration.MukaiSaturationGenericRank

/-!
# The actual saturation of a nonmonic independent triple has rank two

For the original nonsplit extension in Mukai Proposition 5.3, an
independent triple has positive genuine generic rank. A nonmonic
evaluation has rank at most two by the proved torsion-free-source
criterion. Rank one would make its prescribed saturation invertible,
contradicting the proved original extension line bound. Thus its
actual saturation has rank two and its actual torsion-free quotient
is a line bundle, with all original short exact maps retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.MukaiTripleSaturation

open MukaiEvaluationSaturation MukaiEvaluationGenericRank MukaiSaturationGenericRank

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

/-- The rank two is derived for the original nonmonic independent
triple, rather than supplied as a hypothesis. -/
theorem triple_genericRank_eq_two
    (hreg : IsRegular X)
    (s : Fin 3 → cohomologyOverField k f E 0) (hs : LinearIndependent k s)
    (hnmono : ¬ Mono (MukaiSemiIrreducible.evaluation k f E s)) :
    genericRank k f E s = 2 := by
  let hEF : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 3
  let : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  let : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X E
  let : (cokernel (MukaiSemiIrreducible.evaluation k f E s)).IsQuasicoherent :=
    MukaiSaturationSections.evaluation_cokernel_isQuasicoherent k f E s
  have hET : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree E :=
    (isTorsionFree_iff_isFiniteLocallyFree hreg hdim E).mpr hEF
  have hpos := genericRank_pos_of_section_ne_zero k f E hET s 0 (hs.ne_zero 0)
  have hle := triple_genericRank_le_two_of_not_mono k f E s hreg hdim hnmono
  have hne : genericRank k f E s ≠ 1 := by
    intro h1
    let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
        (saturation (MukaiSemiIrreducible.evaluation k f E s)) 1 :=
      saturation_rank_of_genericRank_eq k f E s hreg hdim 1 h1
    have hline : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (saturation (MukaiSemiIrreducible.evaluation k f E s)) :=
      Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace _
    exact (MukaiExtensionLineBounds.evaluation_saturation_not_invertible
      k f hdim hnp S hS hgen hA hB E α i p w hT hnonsplit hα hn s hs) hline
  omega

/-- The original prescribed saturation and its original torsion-free
quotient have derived ranks two and one, with the literal short exact
maps and the retained original three sections. -/
theorem triple_saturation_line_quotient
    (hreg : IsRegular X)
    (s : Fin 3 → cohomologyOverField k f E 0) (hs : LinearIndependent k s)
    (hnmono : ¬ Mono (MukaiSemiIrreducible.evaluation k f E s)) :
    letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 3
    letI : E.IsQuasicoherent :=
      Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
    letI : (cokernel (MukaiSemiIrreducible.evaluation k f E s)).IsQuasicoherent :=
      MukaiSaturationSections.evaluation_cokernel_isQuasicoherent k f E s
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
        (saturation (MukaiSemiIrreducible.evaluation k f E s)) 2 ∧
      SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (torsionFreeQuotient (MukaiSemiIrreducible.evaluation k f E s)) ∧
      (ShortComplex.mk
        (inclusion (MukaiSemiIrreducible.evaluation k f E s))
        (projection (MukaiSemiIrreducible.evaluation k f E s))
        (kernel.condition (projection (MukaiSemiIrreducible.evaluation k f E s)))).ShortExact ∧
      3 ≤ Module.finrank k (cohomologyOverField k f
        (saturation (MukaiSemiIrreducible.evaluation k f E s)) 0) := by
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 3
  let : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  let : (cokernel (MukaiSemiIrreducible.evaluation k f E s)).IsQuasicoherent :=
    MukaiSaturationSections.evaluation_cokernel_isQuasicoherent k f E s
  have hd := triple_genericRank_eq_two
    k f hdim hnp S hS hgen hA hB E α i p w hT hnonsplit hα hn hreg s hs hnmono
  let hQ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (torsionFreeQuotient (MukaiSemiIrreducible.evaluation k f E s)) 1 :=
    quotient_rank_of_genericRank_eq k f E s hreg hdim 3 2 hd
  exact ⟨saturation_rank_of_genericRank_eq k f E s hreg hdim 2 hd,
    Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace _,
    sequence_shortExact _,
    MukaiSaturationSections.evaluation_saturation_h0_lower_bound k f E s hs⟩

end M9Native.MukaiTripleSaturation
