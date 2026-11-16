module

public import M9StacksIntegration.MukaiRankTwoSaturatedQuotient
public import M9StacksIntegration.MukaiRankTwoPencilContradiction
public import M9StacksIntegration.MukaiTwistedQuotientDegree
public import M9StacksIntegration.MukaiGeneratedCartierDegree

/-!
# The actual five-section obstruction after a zero-wedge pair

This layer consumes an actual independent pair of sections, not a line
or rank premise. Its saturation and quotient are constructed, then the
original quotient of Q(D) is untwisted to force degree at least eight.
The independent pair is supplied by the separate five-section exterior
criterion in the final application.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.MukaiFiveSectionObstruction

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]

theorem impossible_of_pair (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (Q : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 2]
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (hlen : letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ(D.subscheme, ⊤) = 2)
    (hgen : MukaiSemiIrreducible.GloballyGenerated Q)
    (hvan : ∀ v : Q ⟶ MukaiBundle.structureModule X, v = 0)
    (hdegree : letI := MukaiGeneratedCartierImage.twist_rank_two D Q
      curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le
        (Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D)) 2 = 12)
    (s : Fin 2 → cohomologyOverField k f
      (Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D)) 0)
    (hs : LinearIndependent k s)
    (hw : ExteriorEvaluation.lambda k f
      (Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D)) 2
      (exteriorPower.ιMulti k 2 s) = 0) : False := by
  let E := Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D)
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 2 :=
    MukaiGeneratedCartierImage.twist_rank_two D Q
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 2
  letI : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  let phi := MukaiSemiIrreducible.evaluation k f E s
  letI : (cokernel phi).IsQuasicoherent :=
    MukaiSaturationSections.evaluation_cokernel_isQuasicoherent k f E s
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X E
  letI := finiteDimensional_cohomologyOverField_of_isProper k f E 0
  obtain ⟨hL,hN,hS,hLtwo⟩ := MukaiRankTwoSaturatedQuotient.pair_line_quotient
    k f E s (isRegular_of_smooth_over_field f)
      (IsCurve.topologicalKrullDim_eq_one f).le hs hw
  letI := hL
  letI := hN
  letI : Epi (MukaiEvaluationSaturation.projection phi) := hS.epi_g
  have hNdegree := MukaiTwistedQuotient.six_add_length_le_degree_quotient f
    (IsCurve.topologicalKrullDim_eq_one f).le hnp D 2 hlen Q
      (MukaiEvaluationSaturation.torsionFreeQuotient phi)
      (MukaiEvaluationSaturation.projection phi) hgen hvan
  rw [show (6 : ℤ) + (2 : ℕ) = 8 by norm_num] at hNdegree
  exact MukaiRankTwoPencilContradiction.degree_twelve f
    (IsCurve.topologicalKrullDim_eq_one f).le hnp hS hdegree hLtwo
      (by simpa only [phi] using hNdegree)

end M9Native.MukaiFiveSectionObstruction
