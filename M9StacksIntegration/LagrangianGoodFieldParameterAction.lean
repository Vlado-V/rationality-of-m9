module

public import M9StacksIntegration.LagrangianExtensionParameterAction

@[expose] public section

/-! The actual original native field action in the raw coordinates of
the unchanged universal incidence family. The coordinate change is
retained explicitly; native and raw parameters are never identified. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace M9Native.LagrangianGoodFieldParameterAction
open LagrangianLinearSections LagrangianExtensionParameterCoordinates

variable (L : Type) [Field L] [Algebra ℂ L]

def originalCoordinates (p : Spec (.of L) ⟶ parameter ℂ) : Spec (.of L) ⟶ parameter ℂ :=
  p ≫ LagrangianParameterCoordinates.coordinateChange.inv

theorem originalCoordinates_projection (p : Spec (.of L) ⟶ parameter ℂ)
    (hp : p ≫ parameterProjection ℂ = Spec.map (CommRingCat.ofHom (algebraMap ℂ L))) :
    originalCoordinates L p ≫ parameterProjection ℂ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ L)) := by
  change (p ≫ LagrangianParameterLinearAction.action ℂ
    LagrangianParameterCoordinates.coordinateUnit⁻¹) ≫ parameterProjection ℂ = _
  rw [Category.assoc, LagrangianParameterLinearAction.action_projection, hp]

/-- The actual native Sp6(L) action conjugated by the proved original
coordinate isomorphism, on the original raw complex parameter scheme. -/
def rawActPoint (g : M9.PrimitiveStabilizer.Sp6 L)
    (p : Spec (.of L) ⟶ parameter ℂ)
    (hp : p ≫ parameterProjection ℂ = Spec.map (CommRingCat.ofHom (algebraMap ℂ L))) :
    Spec (.of L) ⟶ parameter ℂ :=
  PrimitiveFieldMatrixAction.actPoint L g (originalCoordinates L p)
    (originalCoordinates_projection L p hp) ≫ LagrangianParameterCoordinates.coordinateChange.hom

@[reassoc] theorem rawActPoint_projection (g : M9.PrimitiveStabilizer.Sp6 L)
    (p : Spec (.of L) ⟶ parameter ℂ)
    (hp : p ≫ parameterProjection ℂ = Spec.map (CommRingCat.ofHom (algebraMap ℂ L))) :
    rawActPoint L g p hp ≫ parameterProjection ℂ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ L)) := by
  rw [rawActPoint, Category.assoc, LagrangianParameterCoordinates.coordinateChange_projection]
  exact PrimitiveFieldMatrixAction.actPoint_projection L g _ _

/-- Raw action equality is exactly native action equality on the
actual coordinate-changed points, with the same given group element. -/
theorem rawActPoint_eq_iff (g : M9.PrimitiveStabilizer.Sp6 L)
    (p q : Spec (.of L) ⟶ parameter ℂ)
    (hp : p ≫ parameterProjection ℂ = Spec.map (CommRingCat.ofHom (algebraMap ℂ L))) :
    rawActPoint L g p hp = q ↔
      PrimitiveFieldMatrixAction.actPoint L g (originalCoordinates L p)
        (originalCoordinates_projection L p hp) = originalCoordinates L q := by
  constructor
  · intro h
    have hc := congrArg (fun r : Spec (.of L) ⟶ parameter ℂ =>
      r ≫ LagrangianParameterCoordinates.coordinateChange.inv) h
    simpa only [rawActPoint, originalCoordinates, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      using hc
  · intro h
    have hc := congrArg (fun r : Spec (.of L) ⟶ parameter ℂ =>
      r ≫ LagrangianParameterCoordinates.coordinateChange.hom) h
    simpa only [rawActPoint, originalCoordinates, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      using hc

/-- The frozen actual raw matrix formula is preserved by this native
field action, including its inverse-precomposition convention. -/
theorem rawActPoint_rawPoint (g : M9.PrimitiveStabilizer.Sp6 L)
    (M : Matrix (Fin 5) (Fin 14) L) (hM : Function.Surjective M.mulVec) :
    rawActPoint L g (rawPoint L M hM) (rawPoint_projection L M hM) =
      rawPoint L (LagrangianExtensionParameterAction.rawActedMatrix L
        (PrimitiveExtensionFieldBridge.fromOriginal L g) M)
        (LagrangianExtensionParameterAction.rawActed_surjective L
          (PrimitiveExtensionFieldBridge.fromOriginal L g) M hM) := by
  have h := LagrangianExtensionParameterAction.native_action_originalPoint L
    (PrimitiveExtensionFieldBridge.fromOriginal L g) M hM
  rw [PrimitiveExtensionFieldBridge.toOriginal_fromOriginal] at h
  have hc := congrArg (fun r : Spec (.of L) ⟶ parameter ℂ =>
    r ≫ LagrangianParameterCoordinates.coordinateChange.hom) h
  rw [originalPoint_coordinateChange] at hc
  exact hc

end M9Native.LagrangianGoodFieldParameterAction
