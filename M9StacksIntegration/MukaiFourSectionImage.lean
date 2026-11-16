module

public import M9StacksIntegration.MukaiGeneratedCartierDegree
public import M9StacksIntegration.MukaiGeneratedCartierSections
public import M9StacksIntegration.MukaiGeneratedImageH0
public import StacksFrontier.AlgebraicGeometry.Picard.CurveLineBundles.RiemannRoch

/-!
# The literal four-section image in Mukai Lemma 5.4

When Q(D) has four sections and Q has three, one actual extra section
generates a rank-two image with exactly four sections. It is globally
generated, has no trivial quotient, and has degree at most ten.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.MukaiFourSectionImage

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]

/-- All geometric properties refer to the original categorical image
of Q plus one actual section, with no saturation or dimension premise. -/
theorem exists_image (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (Q : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 2]
    (hdeg : curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le Q 2 = 8)
    (hlen : letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ(D.subscheme, ⊤) = 2)
    (hgen : MukaiSemiIrreducible.GloballyGenerated Q)
    (hvan : ∀ v : Q ⟶ MukaiBundle.structureModule X, v = 0)
    (hQ : Module.finrank k (cohomologyOverField k f Q 0) = 3)
    (hTwist : Module.finrank k (cohomologyOverField k f
      (Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D)) 0) = 4) :
    ∃ a : MukaiBundle.structureModule X ⟶
        Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D),
      let F := MukaiGeneratedImage.generatedImage (MukaiGeneratedCartierImage.inclusion D Q) a
      letI := MukaiGeneratedCartierImage.generatedImage_rank_two f D Q a
      Module.finrank k (cohomologyOverField k f F 0) = 4 ∧
        MukaiSemiIrreducible.GloballyGenerated F ∧
        (∀ v : F ⟶ MukaiBundle.structureModule X, v = 0) ∧
        curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le F 2 ≤ 10 := by
  let E := Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D)
  let j := MukaiGeneratedCartierImage.inclusion D Q
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} Q :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree Q 2
  letI : Mono j := MukaiGeneratedCartierImage.inclusion_mono D Q
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 2 :=
    MukaiGeneratedCartierImage.twist_rank_two D Q
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 2
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : Q.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X Q
  letI : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X E
  letI := finiteDimensional_cohomologyOverField_of_isProper k f Q 0
  letI := finiteDimensional_cohomologyOverField_of_isProper k f E 0
  letI := isIso_globalSections_of_isAlgClosed k f
  have hE : Module.finrank k (cohomologyOverField k f E 0) = 4 := hTwist
  obtain ⟨a, ha⟩ := MukaiGeneratedImage.exists_extra_section_h0 f Q E j
    (by rw [hE, hQ])
  refine ⟨a, ?_⟩
  letI := MukaiGeneratedCartierImage.generatedImage_rank_two f D Q a
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (MukaiGeneratedImage.h0_eq_of_postcompose_bijective f Q E j a ha).trans hTwist
  · exact MukaiGeneratedImage.globallyGenerated Q E j a hgen
  · exact MukaiGeneratedCartierImage.hom_structure_eq_zero f D Q hvan a
  · have hd := MukaiGeneratedCartierImage.degree_generated_le f D Q a 2 hlen
    omega

end M9Native.MukaiFourSectionImage
