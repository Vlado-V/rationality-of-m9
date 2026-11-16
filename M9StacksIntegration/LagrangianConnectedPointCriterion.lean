module

public import M9StacksIntegration.LagrangianLinearSectionGenericSmooth
public import M9StacksIntegration.LagrangianGoodPointCriterion
public import M9StacksIntegration.OpenRestrictionPointFiber
public import M9StacksIntegration.ProperSmoothConnectedness

/-! A genuine smooth integral dimension-one point curve of the original
universal incidence gives geometric connectedness and integrality over
its actual canonical proper smooth open. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.LagrangianConnectedPointCriterion

open LagrangianLinearSections LagrangianLinearSectionGenericSmooth
variable (K : Type u) [Field K] [CharZero K]
    (p : Spec (.of K) ⟶ parameter K) (hp : p ≫ parameterProjection K = 𝟙 _)
    [hsm : Smooth (pullback.snd (familyProjection K) p)]
    [hirr : IrreducibleSpace (pullback (C := Scheme.{u}) (familyProjection K) p)]
    (hF : topologicalKrullDim (pullback (C := Scheme.{u}) (familyProjection K) p) = 1)

/-- The actual original good point, lifted into the actual canonical open. -/
def goodPoint : Spec (.of K) ⟶ (goodOpen K).toScheme :=
  OpenRestrictionPointFiber.lift (goodOpen K) p
    (LagrangianGoodPointCriterion.fieldPoint_lands_goodOpen K p hp hF)

@[reassoc (attr := simp)]
theorem goodPoint_comp : goodPoint K p hp hF ≫ (goodOpen K).ι = p :=
  OpenRestrictionPointFiber.lift_comp (goodOpen K) p _

/-- The actual restricted family has the same genuine connected point curve. -/
theorem goodPoint_fiber_connected :
    ConnectedSpace (pullback (C := Scheme.{u}) (restrictedProjection K) (goodPoint K p hp hF)) := by
  let : ConnectedSpace (pullback (C := Scheme.{u}) (familyProjection K) p) := inferInstance
  exact OpenRestrictionPointFiber.fiber_connected (familyProjection K) (goodOpen K) p _

variable [IsAlgClosed K]
include p hp hF hsm hirr

/-- Actual original point-curve geometry forces geometric connectedness
of the entire original family restricted to the canonical good open. -/
theorem restricted_geometricallyConnected : GeometricallyConnected (restrictedProjection K) := by
  let : PreirreducibleSpace (goodOpen K).toScheme :=
    (goodOpen K).ι.isOpenEmbedding.preirreducibleSpace
  let : ConnectedSpace (pullback (C := Scheme.{u}) (restrictedProjection K) (goodPoint K p hp hF)) :=
    goodPoint_fiber_connected K p hp hF
  exact ProperSmoothConnectedness.geometricallyConnected_of_point (restrictedProjection K)
    K (goodPoint K p hp hF)

/-- Every actual fibre over the canonical open is geometrically integral. -/
theorem restricted_geometricallyIntegral : GeometricallyIntegral (restrictedProjection K) := by
  let : GeometricallyConnected (restrictedProjection K) :=
    restricted_geometricallyConnected K p hp hF
  exact SmoothConnectedIntegral.geometricallyIntegral (restrictedProjection K)

end M9Native.LagrangianConnectedPointCriterion
