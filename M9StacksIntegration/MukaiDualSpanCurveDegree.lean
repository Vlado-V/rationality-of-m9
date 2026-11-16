module

public import M9StacksIntegration.MukaiDualSpanDeterminant
public import M9StacksIntegration.MukaiRankTwoExteriorDegree

/-!
# Actual curve degree of the dual span

The actual top exterior isomorphism and the native exterior degree
theorem identify the degree of Q_alpha with that of alpha.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory
open M9Native.MukaiBundle

universe u

namespace M9Native.MukaiDualSpanDeterminant

variable {X : Scheme.{u}}
variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f]
variable (hdim : topologicalKrullDim X ≤ 1)

/-- The original dual-span bundle has the degree of its actual determinant alpha. -/
theorem dualSpan_curveDegree (alpha : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property alpha]
    (s : ULift.{u} (Fin 3) → alpha.sections) (hgen : Epi (netEvaluation alpha s)) :
    letI := dualSpan_rank alpha s hgen
    curveDegree k f hdim (dualSpan alpha s) 2 =
      invertibleCurveDegree k f hdim alpha := by
  letI := dualSpan_rank alpha s hgen
  letI := MukaiTwistBounds.exterior_two_isInvertible (dualSpan alpha s)
  have hd := MukaiTwistBounds.degree_exterior_two f (dualSpan alpha s)
  exact hd.symm.trans
    (invertibleCurveDegree_eq_of_iso k f hdim (dualSpanTopExteriorIso alpha s hgen))

theorem dualSpan_curveDegree_eight (alpha : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property alpha]
    (s : ULift.{u} (Fin 3) → alpha.sections) (hgen : Epi (netEvaluation alpha s))
    (hdegree : invertibleCurveDegree k f hdim alpha = 8) :
    letI := dualSpan_rank alpha s hgen
    curveDegree k f hdim (dualSpan alpha s) 2 = 8 :=
  (dualSpan_curveDegree k f hdim alpha s hgen).trans hdegree

end M9Native.MukaiDualSpanDeterminant
