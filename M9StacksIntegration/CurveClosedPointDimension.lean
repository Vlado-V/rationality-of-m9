module

public import StacksFrontier.AlgebraicGeometry.AmpleDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeries

/-!
# The local dimension at an actual closed curve point

A closed point of an integral one-dimensional scheme cannot be its
generic point: that would make the whole scheme a singleton of dimension
zero. The native specialization/coheight theorem then computes its
actual local-ring dimension. No projective-completion input is needed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

universe u

namespace M9Native.CurveClosedPointDimension

open AlgebraicGeometry TopologicalSpace

theorem closedPoint_ne_genericPoint (X : Scheme.{u}) [IsIntegral X]
    (hdim : topologicalKrullDim X = 1) (x : X) (hx : IsClosed ({x} : Set X)) :
    x ≠ genericPoint X := by
  intro heq
  have hclosure : closure ({x} : Set X) = Set.univ := by
    rw [heq]
    exact genericPoint_spec X
  have huniv : ({x} : Set X) = Set.univ := hx.closure_eq.symm.trans hclosure
  let : Subsingleton X :=
    Set.subsingleton_univ_iff.mp (huniv ▸ Set.subsingleton_singleton)
  have hzero := topologicalKrullDim_zero_of_discreteTopology (X := X)
  rw [hdim] at hzero
  exact absurd hzero (by norm_num)

/-- An actual closed point on the actual integral curve has a
one-dimensional local ring. -/
theorem ringKrullDim_stalk_eq_one {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] (x : X) (hx : IsClosed ({x} : Set X)) :
    ringKrullDim (X.presheaf.stalk x) = 1 :=
  Stacks.AlgebraicGeometry.AmpleDimensionOne.ringKrullDim_stalk_eq_one_of_ne_genericPoint
    X (IsCurve.topologicalKrullDim_eq_one f)
      (closedPoint_ne_genericPoint X (IsCurve.topologicalKrullDim_eq_one f) x hx)

end M9Native.CurveClosedPointDimension
