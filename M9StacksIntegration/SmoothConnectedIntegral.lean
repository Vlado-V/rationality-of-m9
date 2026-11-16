module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! Smooth geometrically connected fibres are genuinely integral.
The native connected-smooth integrality theorem is applied to each
actual field-valued base change; geometric integrality is a conclusion. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.SmoothConnectedIntegral

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [GeometricallyConnected f]

/-- Every actual field-valued pullback of a smooth geometrically
connected morphism is integral. -/
theorem baseChange_integral (K : Type u) [Field K] (p : Spec (.of K) ⟶ Y) :
    IsIntegral (pullback (C := Scheme.{u}) f p) := by
  let : ConnectedSpace (pullback (C := Scheme.{u}) f p) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd f p)
  exact Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (pullback.snd f p)

/-- Smoothness and geometric connectedness imply actual geometric
integrality, without a separate irreducibility premise. -/
theorem geometricallyIntegral : GeometricallyIntegral f := by
  let : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme.{u}) (IsIntegral ·) :=
    ⟨fun e h => have := h; IsIntegral.of_isIso e.hom⟩
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro K _ p
  exact baseChange_integral f K p

end M9Native.SmoothConnectedIntegral
