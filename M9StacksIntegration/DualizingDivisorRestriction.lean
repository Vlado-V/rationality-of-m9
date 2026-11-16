module

public import M9StacksIntegration.FiniteCurveDivisor
public import M9StacksIntegration.CanonicalPencilBounds
public import M9StacksIntegration.CanonicalRestrictionDuality
public import M9StacksIntegration.InvertibleHomCancellation

/-!
# The actual dualizing sheaf separates a length-two divisor

The original ideal inclusion has a one-dimensional Hom space into the
dualizing sheaf: invertible cancellation identifies that space with
the sections of O(D), and absence of a degree-two pencil gives exactly
one such section. Natural Serre duality makes H¹ of the original ideal
inclusion injective; the original exact restriction sequence then makes
H⁰ restriction surjective. The invertibility hypothesis concerns the
actual dualizing sheaf and is supplied for smooth curves by the native
dualizing-sheaf provider, separately from this thin comparison lemma.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

universe u

namespace M9StacksIntegration.DualizingDivisorRestriction

open CategoryTheory AlgebraicGeometry
open M9Native.CurveDivisorSections
open Stacks.Duality (dualizingSheafOverField)

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- Cancellation for the original I_D tensor W orientation, in the
native base-field linear structure, using its actual braiding. -/
theorem finrank_hom_twistDown (f : X ⟶ Spec (.of k)) (W : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property W]
    (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    letI := modulesLinearOverField k f
    Module.finrank k (twistDown D W ⟶ W) =
      Module.finrank k (cohomologyOverField k f (Stacks.Divisors.invertibleSheaf' D) 0) := by
  let := modulesLinearOverField k f
  let e : twistDown D W ≅ Scheme.Modules.tensorObj W (Stacks.Divisors.negativeTwist' D) :=
    Stacks.SheafOfModules.Invertible.tensorProductBraiding X.presheaf
      X.ringCatSheaf.property (Stacks.Divisors.negativeTwist' D) W
  exact (Linear.homCongr k e (Iso.refl W)).finrank_eq.trans
    (InvertibleHomCancellation.finrank_hom_divisor_twist f W D)

/-- The actual native dualizing module restricts surjectively to an
arbitrary length-two closed subscheme on a smooth curve without a
degree-two pencil. The subscheme may be nonreduced. -/
theorem restriction_surjective_of_no_degree_two_pencil
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property (dualizingSheafOverField f)]
    (hdim : topologicalKrullDim X ≤ 1)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 2 1))
    (D : X.IdealSheafData) (hDdim : topologicalKrullDim D.subscheme ≤ 0)
    (hd : letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ(D.subscheme, ⊤) = 2) :
    Function.Surjective (cohomologyOverFieldMap k f (restrictionπ D (dualizingSheafOverField f)) 0) := by
  let := M9Native.FiniteCurveDivisor.isEffectiveCartierDivisor_of_dimension_zero f D hDdim
  let ω : X.Modules := dualizingSheafOverField f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : ω.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X ω
  let : (twistDown D ω).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X _
  have hOD : Module.finrank k
      (cohomologyOverField k f (Stacks.Divisors.invertibleSheaf' D) 0) = 1 :=
    CanonicalPencilBounds.divisor_h0_eq_one_of_no_pencil f hdim 2 hnp D hd
  have hline : letI := modulesLinearOverField k f
      Module.finrank k (twistDown D ω ⟶ ω) = 1 :=
    (finrank_hom_twistDown f ω D).trans hOD
  let : Mono (twistDownι D ω) := (restrictionSequence_shortExact D ω).mono_f
  have hinj := CanonicalRestrictionDuality.injective_cohomology_one_of_mono_of_hom_finrank_eq_one
    f hdim (twistDownι D ω) (isQuasicoherent_of_isCoherent _) (isQuasicoherent_of_isCoherent _) hline
  exact (CohomologyRestriction.surjective_cohomologyMap_iff_injective_successor f
    (restrictionSequence_shortExact D ω) 0).mpr hinj

end M9StacksIntegration.DualizingDivisorRestriction
