module

public import M9StacksIntegration.CanonicalPencilBounds
public import M9StacksIntegration.CanonicalRestrictionDuality
public import M9StacksIntegration.InvertibleHomCancellation
public import M9StacksIntegration.FiniteCurveDivisor
public import M9StacksIntegration.LinearSeriesAddEffectiveDivisor
public import M9StacksIntegration.Private.CurveCanonicalInvertibility
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.VeryAmpleLargeDegree
public import StacksFrontier.AlgebraicGeometry.Picard.CurveLineBundles.RiemannRoch

/-!
# Actual canonical separation on a nonpentagonal smooth curve

The original absence of a degree-five pencil excludes a degree-two
pencil by adding an actual effective divisor. For every actual length-two
closed subscheme, the actual divisor sheaf has one section. Native linear
tensor cancellation computes Hom(omega I_D,omega), and natural Serre
duality proves injectivity on H1. The original restriction exact sequence
then gives the full native degree-two separation predicate.

This isolated current application follows the genuine staged argument in
CanonicalDegreeTwoSeparation, preserving that source unchanged. The audit
binds the reused source and all checked prerequisite objects.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry

universe u

namespace M9Native.MukaiCanonicalSeparation

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]

/-- The actual canonical line separates every actual length-two closed
subscheme on the original curve; there is no embedding or very-ampleness premise. -/
theorem dualizing_surjectsOnDegreeTwo_of_no_degree_five
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1)) :
    SurjectsOnDegreeTwo f (Stacks.Duality.dualizingSheafOverField f) := by
  let hdim := (IsCurve.topologicalKrullDim_eq_one f).le
  letI := isIso_globalSections_of_isAlgClosed k f
  let S : CohenMacaulayCurveSituation.{u} :=
    { k := k
      X := X
      f := f
      proper := inferInstance
      dimension_one := IsCurve.topologicalKrullDim_eq_one f
      isIso_globalSections := inferInstance }
  let ω := Stacks.Duality.dualizingSheafOverField f
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ω :=
    CurveCanonicalInvertibility.dualizing_isInvertible f
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : ω.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X ω
  have hnp₂ := M9StacksIntegration.LinearSeriesAddEffectiveDivisor.no_degree_two_pencil_of_no_degree_five
    f hdim hnp
  refine S.surjectsOnDegreeTwo_of_forall_surjective_subschemeRestrictionπ ω ?_
  intro D hD _hne hd
  letI : Stacks.Divisors.IsEffectiveCartierDivisor D :=
    FiniteCurveDivisor.isEffectiveCartierDivisor_of_dimension_zero f D hD
  have hOD : Module.finrank k
      (cohomologyOverField k f (Stacks.Divisors.divisorSheaf D) 0) = 1 :=
    M9StacksIntegration.CanonicalPencilBounds.divisor_h0_eq_one_of_no_pencil f hdim 2 hnp₂ D hd
  have hline : letI := modulesLinearOverField k f
      Module.finrank k (S.idealTwist D ω ⟶ ω) = 1 := by
    letI := modulesLinearOverField k f
    exact (M9StacksIntegration.InvertibleHomCancellation.finrank_hom_divisor_twist f ω D).trans hOD
  letI : (S.idealTwist D ω).IsCoherent := S.isCoherent_idealTwist D ω
  have hS := S.shortExact_idealTwistι_subschemeRestrictionπ D ω
  letI : Mono (S.idealTwistι D ω) := hS.mono_f
  have hinj := M9StacksIntegration.CanonicalRestrictionDuality.injective_cohomology_one_of_mono_of_hom_finrank_eq_one
    f hdim (S.idealTwistι D ω) (isQuasicoherent_of_isCoherent _)
    (isQuasicoherent_of_isCoherent _) hline
  exact (M9StacksIntegration.CohomologyRestriction.surjective_cohomologyMap_iff_injective_successor f
    hS 0).mpr hinj

end M9Native.MukaiCanonicalSeparation
