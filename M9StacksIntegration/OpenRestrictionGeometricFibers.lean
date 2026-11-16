module

public import M9StacksIntegration.OpenRestrictionPointFiber
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-! Geometric properties proved over an actual base open apply to the
original native residue-field fibres at every point of that open. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.OpenRestrictionGeometricFibers

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

/-- A base-change-stable morphism property on the actual restriction
holds for the actual original residue-field fibre at every point in the open. -/
theorem fiber_property (P : MorphismProperty Scheme.{u})
    [MorphismProperty.IsStableUnderBaseChange P] (h : P (f ∣_ U)) (y : Y) (hy : y ∈ U) :
    P (f.fiberToSpecResidueField y) := by
  let p := Y.fromSpecResidueField y
  have hp : ∀ t, p t ∈ U := fun t => by
    simpa only [p, Scheme.fromSpecResidueField_apply] using hy
  let q := OpenRestrictionPointFiber.lift U p hp
  let e := OpenRestrictionPointFiber.fiberIso f U p hp
  let : MorphismProperty.RespectsIso P :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hbase : P (pullback.snd (f ∣_ U) q) :=
    MorphismProperty.pullback_snd _ _ h
  change P (pullback.snd f p)
  apply (MorphismProperty.cancel_left_of_respectsIso (P := P) e.hom (pullback.snd f p)).mp
  rw [OpenRestrictionPointFiber.fiberIso_hom_snd]
  exact hbase

/-- Actual geometric connectedness on the open gives actual geometric
connectedness of each original native residue-field fibre in it. -/
theorem fiber_geometricallyConnected [GeometricallyConnected (f ∣_ U)]
    (y : Y) (hy : y ∈ U) : GeometricallyConnected (f.fiberToSpecResidueField y) :=
  fiber_property f U (@GeometricallyConnected) inferInstance y hy

/-- Actual geometric integrality on the open gives actual geometric
integrality of each original native residue-field fibre in it. -/
theorem fiber_geometricallyIntegral [GeometricallyIntegral (f ∣_ U)]
    (y : Y) (hy : y ∈ U) : GeometricallyIntegral (f.fiberToSpecResidueField y) :=
  fiber_property f U (@GeometricallyIntegral) inferInstance y hy

end M9Native.OpenRestrictionGeometricFibers
