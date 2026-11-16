module

public import M9StacksIntegration.MukaiResidualTwistBound
public import M9StacksIntegration.MukaiCompleteDualSpanSections
public import M9StacksIntegration.MukaiTwistEuler

/-!
# Mukai Lemma 5.4 on the actual complete residual nets

Every property of Q_alpha is derived from its original complete
evaluation sequence. The genuine residual tensor isomorphism discharges
the canonical inputs. The result concerns the literal native twist and
native H0, for every actual length-two effective Cartier divisor.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory
open M9Native.MukaiBundle M9Native.MukaiBundleDeterminant
open M9Native.MukaiDualSpanSections

universe u

namespace M9Native.MukaiResidualLineBounds

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]

/-- The actual complete residual-net form of Mukai Lemma 5.4. -/
theorem completeDualSpan_twist_h0_le_three
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (alpha beta : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property alpha]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property beta]
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f alpha 0))
    (hgen : Epi (netEvaluation alpha (completeNetSections f alpha b)))
    (e : tensor alpha beta ≅ Stacks.Duality.dualizingSheafOverField f)
    (ha : invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le alpha = 8)
    (hb : invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le beta = 8)
    (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hlen : letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ(D.subscheme, ⊤) = 2) :
    Module.finrank k (cohomologyOverField k f
      (Scheme.Modules.tensorObj (dualSpan alpha (completeNetSections f alpha b))
        (Stacks.Divisors.invertibleSheaf' D)) 0) ≤ 3 := by
  letI := isIso_globalSections_of_isAlgClosed k f
  letI := dualSpan_rank alpha (completeNetSections f alpha b) hgen
  have hd := MukaiDualSpanDeterminant.dualSpan_curveDegree_eight k f
    (IsCurve.topologicalKrullDim_eq_one f).le alpha (completeNetSections f alpha b) hgen ha
  have hgenerated := MukaiSemiIrreducible.dualSpan_globallyGenerated alpha
    (completeNetSections f alpha b) hgen
  have hvan := hom_structure_subsingleton_of_complete_net f alpha b hgen
  exact bundle_twist_h0_le_three f hg hnp alpha beta e ha hb D hlen
    (dualSpan alpha (completeNetSections f alpha b)) hd hgenerated
      (fun v => hvan.elim _ _)
      (MukaiDualSpanSections.completeDualSpan_h0_eq_three f hnp alpha b hgen ha)

/-- The Euler difference for the same original complete dual span. -/
theorem completeDualSpan_twist_h0_sub_h1_eq_neg_four
    (hg : genus f = 9) (alpha : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property alpha]
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f alpha 0))
    (hgen : Epi (netEvaluation alpha (completeNetSections f alpha b)))
    (ha : invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le alpha = 8)
    (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hlen : letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ(D.subscheme, ⊤) = 2) :
    (Module.finrank k (cohomologyOverField k f
      (Scheme.Modules.tensorObj (dualSpan alpha (completeNetSections f alpha b))
        (Stacks.Divisors.invertibleSheaf' D)) 0) : ℤ) -
      Module.finrank k (cohomologyOverField k f
      (Scheme.Modules.tensorObj (dualSpan alpha (completeNetSections f alpha b))
        (Stacks.Divisors.invertibleSheaf' D)) 1) = -4 := by
  letI := dualSpan_rank alpha (completeNetSections f alpha b) hgen
  have hd := MukaiDualSpanDeterminant.dualSpan_curveDegree_eight k f
    (IsCurve.topologicalKrullDim_eq_one f).le alpha (completeNetSections f alpha b) hgen ha
  exact MukaiTwistBounds.h0_sub_h1_twist_eq_neg_four f hg D hlen
    (dualSpan alpha (completeNetSections f alpha b)) hd

end M9Native.MukaiResidualLineBounds
