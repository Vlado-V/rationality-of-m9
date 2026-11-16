module

public import M9StacksIntegration.CurveDerivativeSourceKernel
public import M9StacksIntegration.SmoothCurveCanonicalDifferentials

/-!
# The actual source derivative kernel for small-degree genus-nine covers

The genuine native canonical/cotangent comparison derives degree16.
The actual normal-boundary quotient therefore bounds the literal H1
source kernel by13+2d, at most23 for an actual map degree at most5.
No cohomology value, normal length, moduli dimension or deformation-image
identification is a premise.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry
open M9Native.CurveTangentLineGeometry M9Native.CurveDerivativeSourceKernel
open M9Native.PencilProjectiveLineGeometry

universe u

namespace M9Native.GenusNineP1SourceKernel

attribute [local instance] isCurve_projectiveSpaceOver_one CurveP1NormalSections.line_smooth

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
variable (hg : genus f = 9)
variable (g : X ⟶ Line k) (hcomm : g ≫ toBase k = f)
variable (hnc : ¬ ∃ y : Line k, ∀ x : X, g.base x = y)

include hg hnc

/-- The original H1 derivative kernel has dimension at most13+2d. -/
theorem sourceKernel_finrank_le :
    Module.finrank k (sourceKernel f (toBase k) g hcomm) ≤
      13 + 2 * PencilDegreePullback.curveMapDegree f (toBase k) g hcomm hnc := by
  let := differentials_rank_one f
  have hd : curveDegree k f (IsCurve.topologicalKrullDim_eq_one (f := f)).le
      (Scheme.Hom.relativeDifferentials f) 1 = 16 := by
    have h := SmoothCurveCanonicalDifferentials.differentials_curveDegree_of_isAlgClosed
      f (IsCurve.topologicalKrullDim_eq_one (f := f)).le
    rw [hg] at h
    norm_num at h
    exact h
  have hle := sourceKernel_p1_finrank_degree_le f g hcomm hnc
    (by rw [hd]; norm_num)
  rw [hd] at hle
  have hz : (Module.finrank k (sourceKernel f (toBase k) g hcomm) : ℤ) ≤
      (13 + 2 * PencilDegreePullback.curveMapDegree f (toBase k) g hcomm hnc : ℕ) := by
    push_cast
    omega
  exact_mod_cast hz

/-- For genuine degree at most five the original source H1 kernel
has dimension at most twenty-three. -/
theorem sourceKernel_finrank_le_twenty_three
    (hd : PencilDegreePullback.curveMapDegree f (toBase k) g hcomm hnc ≤ 5) :
    Module.finrank k (sourceKernel f (toBase k) g hcomm) ≤ 23 := by
  have h := sourceKernel_finrank_le f hg g hcomm hnc
  omega

end M9Native.GenusNineP1SourceKernel
