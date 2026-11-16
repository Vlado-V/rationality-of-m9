module

public import M9StacksIntegration.MukaiCartierTwistDegree
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Picard.CurveLineBundles.RiemannRoch

/-!
# The actual Euler difference of Q(D)

For the rank-two degree-eight bundle and a length-two divisor on a
genus-nine curve, native Riemann-Roch gives h0(Q(D))−h1(Q(D))=−4.
No Euler characteristic or cohomology dimension is supplied as data.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.MukaiTwistBounds

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f]

/-- The negative-four Euler difference is computed on the original
native cohomology spaces of the literal positive divisor twist. -/
theorem h0_sub_h1_twist_eq_neg_four
    (hg : genus f = 9)
    (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hlen : letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ(D.subscheme, ⊤) = 2)
    (Q : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 2]
    (hdegree : curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le Q 2 = 8) :
    (Module.finrank k (cohomologyOverField k f
        (Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D)) 0) : ℤ) -
      Module.finrank k (cohomologyOverField k f
        (Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D)) 1) = -4 := by
  let E := Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D)
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 2 :=
    MukaiGeneratedCartierImage.twist_rank_two D Q
  letI := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 2
  letI := isIso_globalSections_of_isAlgClosed k f
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X E
  have hdeg : curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le E 2 = 12 := by
    have h := MukaiGeneratedCartierImage.degree_twist f D Q 2 hlen
    change curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le E 2 = _ at h
    omega
  have hχ := eulerCharacteristic_eq_curveDegree_add_genus k f
    (IsCurve.topologicalKrullDim_eq_one f).le E 2
  have ht : eulerCharacteristic k f E =
      (Module.finrank k (cohomologyOverField k f E 0) : ℤ) -
        Module.finrank k (cohomologyOverField k f E 1) :=
    finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k f E
      (isZero_cohomologyOverField_two_le k f (IsCurve.topologicalKrullDim_eq_one f).le E)
  rw [hg, hdeg] at hχ
  change (Module.finrank k (cohomologyOverField k f E 0) : ℤ) -
    Module.finrank k (cohomologyOverField k f E 1) = -4
  omega

end M9Native.MukaiTwistBounds
