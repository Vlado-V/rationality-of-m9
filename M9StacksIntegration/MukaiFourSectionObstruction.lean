module

public import M9StacksIntegration.MukaiRankTwoSaturatedQuotient
public import M9StacksIntegration.MukaiRankTwoPencilContradiction
public import M9StacksIntegration.MukaiGeneratedQuotient
public import StacksFrontier.AlgebraicGeometry.CurveDegreeDeterminant
public import StacksFrontier.AlgebraicGeometry.Picard.CurveLineBundles.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular

/-!
# The actual four-section contradiction

The independent zero-wedge pair, saturated line, and line quotient are
constructed from the original exterior evaluation. No line filtration
is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.MukaiFourSectionObstruction

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]

/-- The rank-two determinant criterion and original quotient degrees
exclude four sections in a generated bundle of degree at most ten. -/
theorem impossible (F : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (hdegree : curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le F 2 ≤ 10)
    (hgen : MukaiSemiIrreducible.GloballyGenerated F)
    (hvan : ∀ v : F ⟶ MukaiBundle.structureModule X, v = 0)
    (hsections : 4 ≤ Module.finrank k (cohomologyOverField k f F 0))
    (hdet : Module.finrank k
      (cohomologyOverField k f (Scheme.Modules.exteriorPower F 2) 0) ≤ 4) : False := by
  letI := isIso_globalSections_of_isAlgClosed k f
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F 2
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : F.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X F
  letI := finiteDimensional_cohomologyOverField_of_isProper k f F 0
  letI := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self F 2
  letI := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (Scheme.Modules.exteriorPower F 2) 1
  letI : (Scheme.Modules.exteriorPower F 2).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X _
  letI := finiteDimensional_cohomologyOverField_of_isProper k f
    (Scheme.Modules.exteriorPower F 2) 0
  obtain ⟨L,N,j,q,w,hL,hN,hS,hLtwo⟩ :=
    MukaiRankTwoSaturatedQuotient.exists_saturated_line_quotient k f F
      (isRegular_of_smooth_over_field f) (IsCurve.topologicalKrullDim_eq_one f).le
      hsections hdet
  letI := hL
  letI := hN
  letI : Epi q := hS.epi_g
  letI : N.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X N
  letI := finiteDimensional_cohomologyOverField_of_isProper k f N 0
  have hNtwo := MukaiGeneratedQuotient.two_le_h0_of_generated_no_unit_hom
    f F N hgen q hvan
  exact MukaiRankTwoPencilContradiction.degree_le_ten f
    (IsCurve.topologicalKrullDim_eq_one f).le hnp hS hdegree hLtwo hNtwo

end M9Native.MukaiFourSectionObstruction
