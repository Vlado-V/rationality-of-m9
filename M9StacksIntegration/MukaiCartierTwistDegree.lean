module

public import M9StacksIntegration.MukaiGeneratedCartierDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegreeTwist

/-!
# Degree of the original rank-two Cartier twist

The formula is obtained from the native tensor-product degree theorem
and the native degree/length equality for the actual Cartier divisor.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.MukaiGeneratedCartierImage

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f]

theorem degree_twist (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (Q : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 2]
    (d : ℕ) (hlen : letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ(D.subscheme, ⊤) = d) :
    letI := twist_rank_two D Q
    curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le
      (Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D)) 2 =
        curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le Q 2 + 2 * d := by
  letI : Algebra k Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
  let L := Stacks.Divisors.invertibleSheaf' D
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L :=
    Stacks.Divisors.invertibleSheaf_isInvertible D
  letI := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X L
  letI := twist_rank_two D Q
  have hdeg := curveDegree_tensorSheaf_eq_add k f
    (IsCurve.topologicalKrullDim_eq_one f).le Q L 2 1
  have hL := invertibleCurveDegree_invertibleSheaf_eq_finrank_globalSections
    k f (IsCurve.topologicalKrullDim_eq_one f).le D
  change invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le L =
    (Module.finrank k Γ(D.subscheme, ⊤) : ℤ) at hL
  rw [hlen, invertibleCurveDegree_eq_curveDegree] at hL
  change curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le
      (Scheme.Modules.tensorObj Q L) 2 =
    (1 : ℤ) * curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le Q 2 +
      (2 : ℤ) * curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le L 1 at hdeg
  simpa only [hL, one_mul] using hdeg

end M9Native.MukaiGeneratedCartierImage
