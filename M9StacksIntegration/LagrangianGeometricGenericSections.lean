module

public import M9StacksIntegration.LagrangianBertiniPoint
public import M9StacksIntegration.LagrangianConnectedPointCriterion
public import M9StacksIntegration.OpenRestrictionGeometricFibers

/-! Genuine geometric connectedness and integrality of the original
universal LG five-hyperplane family over its actual canonical smooth
open, derived from the constructed Bertini point and actual component
count spreading. No connected-fibre or generic-integrality premise. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.LagrangianGeometricGenericSections

open LagrangianLinearSections LagrangianLinearSectionGenericSmooth
open SmoothIntegralHyperplaneCuts LagrangianBertiniPoint
variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]

/-- The original canonical good-open family is genuinely geometrically
connected, by its actual constructed integral point curve. -/
instance restricted_geometricallyConnected : GeometricallyConnected (restrictedProjection K) :=
  LagrangianConnectedPointCriterion.restricted_geometricallyConnected K (parameterPoint K)
    (parameterPoint_projection K) (pointFibre_dimension K)

/-- The original canonical good-open family is genuinely geometrically integral. -/
instance restricted_geometricallyIntegral : GeometricallyIntegral (restrictedProjection K) :=
  SmoothConnectedIntegral.geometricallyIntegral (restrictedProjection K)

/-- Every original native residue-field fibre over the actual good open
is geometrically integral. -/
theorem fibre_geometricallyIntegral (y : parameter K) (hy : y ∈ goodOpen K) :
    GeometricallyIntegral ((familyProjection K).fiberToSpecResidueField y) := by
  let : GeometricallyIntegral (familyProjection K ∣_ goodOpen K) :=
    restricted_geometricallyIntegral K
  exact OpenRestrictionGeometricFibers.fiber_geometricallyIntegral
    (familyProjection K) (goodOpen K) y hy

omit [IsAlgClosed K] in
/-- The genuine canonical good open contains the actual generic parameter. -/
theorem genericPoint_mem_goodOpen : genericPoint (parameter K) ∈ goodOpen K := by
  apply ((genericPoint_spec (parameter K)).mem_open_set_iff (goodOpen K).isOpen).mpr
  simpa only [Set.univ_inter] using LagrangianLinearSectionGenericSmooth.goodOpen_nonempty K

/-- The original generic fibre is genuinely geometrically integral. -/
theorem generic_fibre_geometricallyIntegral :
    GeometricallyIntegral ((familyProjection K).fiberToSpecResidueField (genericPoint (parameter K))) :=
  fibre_geometricallyIntegral K _ (genericPoint_mem_goodOpen K)

/-- Every actual field-valued pullback of the canonical open family is integral. -/
theorem baseChange_integral (L : Type u) [Field L]
    (p : Spec (.of L) ⟶ (goodOpen K).toScheme) :
    IsIntegral (pullback (C := Scheme.{u}) (restrictedProjection K) p) :=
  SmoothConnectedIntegral.baseChange_integral (restrictedProjection K) L p

/-- Every actual field-valued pullback of the canonical open family is connected. -/
theorem baseChange_connected (L : Type u) [Field L]
    (p : Spec (.of L) ⟶ (goodOpen K).toScheme) :
    ConnectedSpace (pullback (C := Scheme.{u}) (restrictedProjection K) p) :=
  GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd (restrictedProjection K) p)

end M9Native.LagrangianGeometricGenericSections
