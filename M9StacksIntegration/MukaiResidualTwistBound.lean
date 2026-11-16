module

public import M9StacksIntegration.MukaiResidualLineBounds
public import M9StacksIntegration.MukaiCanonicalTwistSectionBound

/-!
# Actual divisor twist bound from the genuine residual Mukai data

The canonical hypotheses of the two-case core are proved using the
original degree-eight residual nets and their actual tensor isomorphism.
The resulting statement has no canonical invertibility/degree premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory
open M9Native.MukaiBundleDeterminant

universe u

namespace M9Native.MukaiResidualLineBounds

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]

theorem bundle_twist_h0_le_three
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (alpha beta : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property alpha]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property beta]
    (e : tensor alpha beta ≅ Stacks.Duality.dualizingSheafOverField f)
    (ha : invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le alpha = 8)
    (hb : invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le beta = 8)
    (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hlen : letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ(D.subscheme, ⊤) = 2)
    (Q : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 2]
    (hdegree : curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le Q 2 = 8)
    (hgen : MukaiSemiIrreducible.GloballyGenerated Q)
    (hvan : ∀ v : Q ⟶ M9Native.MukaiBundle.structureModule X, v = 0)
    (hQ : Module.finrank k (cohomologyOverField k f Q 0) = 3) :
    Module.finrank k (cohomologyOverField k f
      (Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D)) 0) ≤ 3 := by
  letI := canonical_isInvertible f alpha beta e
  have hω := canonical_degree f (IsCurve.topologicalKrullDim_eq_one f).le
    alpha beta e ha hb
  have hC : invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le
      (Stacks.Duality.dualizingSheafOverField f) = 2 * (genus f : ℤ) - 2 := by
    rw [hω, hg]
    norm_num
  exact MukaiCanonicalTwistBounds.bundle_twist_h0_le_three f hC hg hnp D hlen
    Q hdegree hgen hvan hQ

end M9Native.MukaiResidualLineBounds
