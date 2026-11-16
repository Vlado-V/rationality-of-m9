module

public import M9StacksIntegration.MukaiTwistedQuotient
public import M9StacksIntegration.MukaiPencilDegreeBounds
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegreeTwist
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Picard.CurveLineBundles.RiemannRoch

/-!
# Degree of the original quotient after cancelling a Cartier twist

The negative twist is the actual ideal sheaf. Its degree is the negative
of the finite divisor length by the actual evaluation isomorphism.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open M9StacksIntegration.InvertibleHomCancellation (tensorRight)

universe u

namespace M9Native.MukaiTwistedQuotient

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f]
variable (hdim : topologicalKrullDim X ≤ 1)

/-- The degree of the original Cartier ideal is minus the actual divisor length. -/
theorem degree_negativeTwist (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (d : ℕ) (hlen : letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ(D.subscheme, ⊤) = d) :
    invertibleCurveDegree k f hdim (Stacks.Divisors.negativeTwist' D) = -(d : ℤ) := by
  letI : Algebra k Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
  let L := Stacks.Divisors.invertibleSheaf' D
  let I := Stacks.Divisors.negativeTwist' D
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L :=
    Stacks.Divisors.invertibleSheaf_isInvertible D
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property I :=
    Stacks.Divisors.isInvertible_negativeTwist D
  letI : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property I :=
    Stacks.Divisors.isTensorInvertible_negativeTwist D
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (Scheme.Modules.tensorObj L I) :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf
      X.ringCatSheaf.property L I
  have hprod := invertibleCurveDegree_tensorSheaf_eq_add k f hdim L I
  change invertibleCurveDegree k f hdim (Scheme.Modules.tensorObj L I) =
    invertibleCurveDegree k f hdim L + invertibleCurveDegree k f hdim I at hprod
  have hzero := invertibleCurveDegree_eq_zero_of_iso_unit k f hdim
    (Scheme.Modules.tensorObj L I) (Stacks.SheafOfModules.Scheme.evaluationIso X I)
  have hpos := invertibleCurveDegree_invertibleSheaf_eq_finrank_globalSections
    k f hdim D
  change invertibleCurveDegree k f hdim L =
    (Module.finrank k Γ(D.subscheme, ⊤) : ℤ) at hpos
  rw [hlen] at hpos
  change invertibleCurveDegree k f hdim I = -(d : ℤ)
  omega

/-- A line quotient of Q(D), for generated Q without a trivial quotient,
has degree at least six plus the length of D. -/
theorem six_add_length_le_degree_quotient [IsAlgClosed k] [IsCurve k f] [Smooth f]
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (d : ℕ) (hlen : letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ(D.subscheme, ⊤) = d)
    (Q N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N]
    (q : Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D) ⟶ N) [Epi q]
    (hgen : MukaiSemiIrreducible.GloballyGenerated Q)
    (hvan : ∀ v : Q ⟶ MukaiBundle.structureModule X, v = 0) :
    (6 : ℤ) + d ≤ invertibleCurveDegree k f hdim N := by
  letI := isIso_globalSections_of_isAlgClosed k f
  let I := Stacks.Divisors.negativeTwist' D
  let L := (tensorRight I).obj N
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property I :=
    Stacks.Divisors.isInvertible_negativeTwist D
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L :=
    Stacks.SheafOfModules.Invertible.tensorProduct_isInvertible X.presheaf
      X.ringCatSheaf.property N I
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : L.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X L
  letI := finiteDimensional_cohomologyOverField_of_isProper k f L 0
  have htwo := two_le_h0_untwist D f Q N q hgen hvan
  have hL := MukaiPencilDegreeBounds.six_le_degree_of_two_sections f hdim hnp L htwo
  have hI := degree_negativeTwist f hdim D d hlen
  have hprod := invertibleCurveDegree_tensorSheaf_eq_add k f hdim N I
  change invertibleCurveDegree k f hdim L =
    invertibleCurveDegree k f hdim N + invertibleCurveDegree k f hdim I at hprod
  change invertibleCurveDegree k f hdim I = -(d : ℤ) at hI
  omega

end M9Native.MukaiTwistedQuotient
