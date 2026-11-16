module

public import M9StacksIntegration.MukaiCanonicalTwistBounds
public import M9StacksIntegration.MukaiFourSectionImage
public import M9StacksIntegration.MukaiFourSectionObstruction
public import M9StacksIntegration.MukaiFiveSectionObstruction
public import M9StacksIntegration.MukaiRankTwoFiveCriterion
public import M9StacksIntegration.MukaiCartierTwistDegree
public import M9StacksIntegration.MukaiRankTwoExteriorDegree

/-!
# Actual two-case twist bound with canonical data

This helper takes the actual native dualizing sheaf invertibility and
canonical degree. Genuine residual-net data discharges these in a
separate wrapper; the arbitrary smooth-curve wrapper also remains.
Both cases use the actual native sheaves. The four-section case uses the
literal image of Q plus an extra section. The five-section case uses an
actual independent zero-wedge pair in Q(D), its original saturation and
torsion-free quotient, and the untwisted quotient of Q.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open M9Native.MukaiTwistBounds (exterior_two_isInvertible degree_exterior_two)

universe u

namespace M9Native.MukaiCanonicalTwistBounds

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
  (Stacks.Duality.dualizingSheafOverField f)]
variable (hcanonicalDegree : invertibleCurveDegree k f
  (IsCurve.topologicalKrullDim_eq_one f).le
    (Stacks.Duality.dualizingSheafOverField f) = 2 * (genus f : ℤ) - 2)
include hcanonicalDegree

/-- A generated rank-two degree-eight bundle without a trivial quotient
has at most three sections. The lower bound is separate. -/
theorem h0_le_three_of_degree_eight
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (Q : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 2]
    (hdeg : curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le Q 2 = 8)
    (hgen : MukaiSemiIrreducible.GloballyGenerated Q)
    (hvan : ∀ v : Q ⟶ MukaiBundle.structureModule X, v = 0) :
    Module.finrank k (cohomologyOverField k f Q 0) ≤ 3 := by
  by_contra h
  letI := exterior_two_isInvertible Q
  have hd := degree_exterior_two f Q
  have hb := h0_le_four_of_degree_le_ten f
    (IsCurve.topologicalKrullDim_eq_one f).le hcanonicalDegree hg hnp
      (Scheme.Modules.exteriorPower Q 2) (by omega)
  exact MukaiFourSectionObstruction.impossible f Q hnp (by omega) hgen hvan
    (by omega) hb

/-- **Mukai Lemma 5.4, rank-two form.** Every actual length-two
effective Cartier divisor satisfies h0(Q(D))≤3. -/
theorem bundle_twist_h0_le_three
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hlen : letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ(D.subscheme, ⊤) = 2)
    (Q : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 2]
    (hdeg : curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le Q 2 = 8)
    (hgen : MukaiSemiIrreducible.GloballyGenerated Q)
    (hvan : ∀ v : Q ⟶ MukaiBundle.structureModule X, v = 0)
    (hQ : Module.finrank k (cohomologyOverField k f Q 0) = 3) :
    Module.finrank k (cohomologyOverField k f
      (Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D)) 0) ≤ 3 := by
  let E := Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D)
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 2 :=
    MukaiGeneratedCartierImage.twist_rank_two D Q
  letI := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 2
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X E
  letI := finiteDimensional_cohomologyOverField_of_isProper k f E 0
  have hEdeg : curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le E 2 = 12 := by
    have hd := MukaiGeneratedCartierImage.degree_twist f D Q 2 hlen
    change curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le E 2 = _ at hd
    omega
  by_contra h
  change ¬ Module.finrank k (cohomologyOverField k f E 0) ≤ 3 at h
  by_cases hfour : Module.finrank k (cohomologyOverField k f E 0) = 4
  · obtain ⟨a,hF,hgenerated,hnohom,hFdeg⟩ :=
      MukaiFourSectionImage.exists_image f D Q hdeg hlen hgen hvan hQ hfour
    let F := MukaiGeneratedImage.generatedImage (MukaiGeneratedCartierImage.inclusion D Q) a
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2 :=
      MukaiGeneratedCartierImage.generatedImage_rank_two f D Q a
    change Module.finrank k (cohomologyOverField k f F 0) = 4 at hF
    change curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le F 2 ≤ 10 at hFdeg
    letI := exterior_two_isInvertible F
    have hd := degree_exterior_two f F
    have hb := h0_le_four_of_degree_le_ten f
      (IsCurve.topologicalKrullDim_eq_one f).le hcanonicalDegree hg hnp
        (Scheme.Modules.exteriorPower F 2) (by omega)
    exact MukaiFourSectionObstruction.impossible f F hnp hFdeg hgenerated hnohom
      (by omega) hb
  · letI := exterior_two_isInvertible E
    letI : (Scheme.Modules.exteriorPower E 2).IsCoherent :=
      Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X _
    letI := finiteDimensional_cohomologyOverField_of_isProper k f
      (Scheme.Modules.exteriorPower E 2) 0
    have hd := degree_exterior_two f E
    have hb := h0_le_five_of_degree_twelve f
      (IsCurve.topologicalKrullDim_eq_one f).le hcanonicalDegree hg hnp
        (Scheme.Modules.exteriorPower E 2) (hd.trans hEdeg)
    obtain ⟨a,b,hab,hw⟩ :=
      MukaiRankTwoFiveCriterion.exists_two_sections_zero_exteriorEvaluation k f E
        (by omega) hb
    exact MukaiFiveSectionObstruction.impossible_of_pair f D Q hnp hlen hgen hvan
      hEdeg ![a,b] hab hw

end M9Native.MukaiCanonicalTwistBounds
