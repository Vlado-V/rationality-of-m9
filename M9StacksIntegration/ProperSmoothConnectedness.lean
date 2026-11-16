module

public import M9StacksIntegration.SmoothConnectedIntegral
public import M9StacksIntegration.ConnectedGeometricPoint
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FibreConnectedComponents.LocalConstancy
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-! A genuine connected field-valued fibre of a proper smooth morphism
over a preconnected base forces geometric connectedness of every fibre.
The native locally constant geometric component count supplies the
spreading step; geometric integrality then follows from smoothness. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.ProperSmoothConnectedness

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- For a proper smooth family on a preconnected base, one actual
connected fibre over a separably closed field forces all actual fibres
to be geometrically connected. -/
theorem geometricallyConnected_of_point [IsProper f] [Smooth f] [PreconnectedSpace Y]
    (K : Type u) [Field K] [IsSepClosed K] (p : Spec (.of K) ⟶ Y)
    [ConnectedSpace (pullback (C := Scheme.{u}) f p)] : GeometricallyConnected f := by
  let : GeometricallyReduced f := geometricallyReduced_of_smooth f
  have hlc := isLocallyConstant_numGeometricConnectedComponents f
    ((geometricallyReduced_iff_forall_isAlgClosed f).mp inferInstance)
  exact ConnectedGeometricPoint.geometricallyConnected_of_locallyConstant_count f hlc K p

/-- The same actual point criterion gives geometric integrality of the
whole proper smooth family, with no irreducibility premise on other fibres. -/
theorem geometricallyIntegral_of_point [IsProper f] [Smooth f] [PreconnectedSpace Y]
    (K : Type u) [Field K] [IsSepClosed K] (p : Spec (.of K) ⟶ Y)
    [ConnectedSpace (pullback (C := Scheme.{u}) f p)] : GeometricallyIntegral f := by
  let : GeometricallyConnected f := geometricallyConnected_of_point f K p
  exact SmoothConnectedIntegral.geometricallyIntegral f

end M9Native.ProperSmoothConnectedness
