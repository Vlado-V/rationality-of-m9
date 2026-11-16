module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.ConnectedComponents
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GeometricallyConnectedFibres
public import Mathlib.Topology.LocallyConstant.Basic

/-! An actual connected fibre over a separably closed field detects
geometric connectedness and geometric component count one in the original
native residue-field fibre. No rationality or residue-field-isomorphism
premise is required. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.ConnectedGeometricPoint

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A connected actual point pullback over a separably closed field
makes the original native fibre geometrically connected. -/
theorem point_fiber_geometricallyConnected (K : Type u) [Field K] [IsSepClosed K]
    (p : Spec (.of K) ⟶ Y)
    [ConnectedSpace (pullback (C := Scheme.{u}) f p)] :
    GeometricallyConnected (f.fiberToSpecResidueField (p (IsLocalRing.closedPoint K))) := by
  let : GeometricallyConnected (pullback.snd f p) :=
    (geometricallyConnected_iff_connectedSpace K (pullback.snd f p)).mpr inferInstance
  have hsets := congrArg (fun A : Set (Spec (.of K)) => IsLocalRing.closedPoint K ∈ A)
    (geometricallyConnected_fiber_locus_pullback f p)
  exact hsets.mp (inferInstance :
    GeometricallyConnected ((pullback.snd f p).fiberToSpecResidueField (IsLocalRing.closedPoint K)))

/-- The original native fibre at the image of the actual connected
separably closed point has geometric component count one. -/
theorem point_count_one (K : Type u) [Field K] [IsSepClosed K]
    (p : Spec (.of K) ⟶ Y)
    [ConnectedSpace (pullback (C := Scheme.{u}) f p)] :
    numGeometricConnectedComponents f (p (IsLocalRing.closedPoint K)) = 1 :=
  (geometricallyConnected_iff_numGeometricConnectedComponents_eq_one f _).mp
    (point_fiber_geometricallyConnected f K p)

/-- On a preconnected base, an actually locally constant geometric
component count and one actual connected separably closed point fibre
force geometric connectedness of the entire morphism. -/
theorem geometricallyConnected_of_locallyConstant_count [PreconnectedSpace Y]
    (hlc : IsLocallyConstant (numGeometricConnectedComponents f))
    (K : Type u) [Field K] [IsSepClosed K] (p : Spec (.of K) ⟶ Y)
    [ConnectedSpace (pullback (C := Scheme.{u}) f p)] : GeometricallyConnected f := by
  apply (GeometricallyConnected.iff_geometricallyConnected_fiber f).mpr
  intro y
  apply (geometricallyConnected_iff_numGeometricConnectedComponents_eq_one f y).mpr
  exact (hlc.apply_eq_of_preconnectedSpace y (p (IsLocalRing.closedPoint K))).trans
    (point_count_one f K p)

end M9Native.ConnectedGeometricPoint
