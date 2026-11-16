module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeries
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcDescentProperties.NoetherianNormalDecomposition
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.AutomaticProperties

/-!
# Actual smooth connected schemes of dimension one are native curves

The original proper scheme is Noetherian. Smoothness gives regularity
and normality; connected normal Noetherian schemes are irreducible.
Thus integrality and the native IsCurve class are derived from the
original geometric conditions, with no curve-class premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

universe u

namespace M9Native.SmoothConnectedCurve

open CategoryTheory AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The original smooth proper connected scheme is integral. -/
theorem isIntegral_of_smooth_connected (f : X ⟶ Spec (.of k))
    [IsProper f] [Smooth f] [ConnectedSpace X] : IsIntegral X := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := {}
  let hN : IsNormal X := isNormal_of_isRegular X (isRegular_of_smooth_over_field f)
  let : IsNormal X := hN
  let : IrreducibleSpace X := irreducibleSpace_of_isNormal_of_connectedSpace X hN
  exact (isIntegral_iff_irreducibleSpace_and_isReduced X).mpr ⟨inferInstance, inferInstance⟩

/-- Native curve structure follows from the actual smooth, proper,
connected and dimension-one conditions. -/
theorem isCurve_of_smooth_connected (f : X ⟶ Spec (.of k))
    [IsProper f] [Smooth f] [ConnectedSpace X] (hdim : topologicalKrullDim X = 1) :
    IsCurve k f := by
  let : IsIntegral X := isIntegral_of_smooth_connected f
  let : IsVariety k f := IsVariety.mk
  exact (isCurve_iff k f).mpr ⟨inferInstance, hdim⟩

/-- Geometric connectedness over the original field supplies ordinary
connectedness, so no separate integrality or curve premise is needed. -/
theorem isCurve_of_smooth_geometricallyConnected (f : X ⟶ Spec (.of k))
    [IsProper f] [Smooth f] [GeometricallyConnected f] (hdim : topologicalKrullDim X = 1) :
    IsCurve k f := by
  let : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton (f := f)
  exact isCurve_of_smooth_connected f hdim

/-- The native moduli-point condition on the original constant-function
map is another actual source of connectedness and hence curve structure. -/
theorem isCurve_of_smooth_constantFunctions (f : X ⟶ Spec (.of k))
    [IsProper f] [Smooth f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hdim : topologicalKrullDim X = 1) : IsCurve k f := by
  let : ConnectedSpace X := connectedSpace_of_isIso_globalSections k f
  exact isCurve_of_smooth_connected f hdim

end M9Native.SmoothConnectedCurve
