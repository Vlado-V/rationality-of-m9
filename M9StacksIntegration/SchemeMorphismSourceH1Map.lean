module

public import M9StacksIntegration.SchemeMorphismSourceObstruction
public import M9StacksIntegration.StandardSchemeTangent

/-!
# The actual source-forgetting map to original tangent H1

The source is the literal native morphism-deformation tangent module at
ULift k. The map is actual endpoint forgetting followed by the checked
original standard source classifier and evaluation-natural H1 comparison.
No image, kernel, rank or parameter-space identification is asserted here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry Deformation Deformation.Examples

universe u

namespace M9Native.SchemeMorphismSourceH1

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
  [IsCurve k pX] [Smooth pX] (g : X ⟶ Y) (hg : g ≫ pY = pX)

/-- The literal original source tangent module for morphism deformations. -/
abbrev morphismTangentModule :=
  tangentModuleAt.{u,u,u}
    (BasedCategory.ofFunctor
      (schemeMorphismDeformationCategoryProjection (Λ := k) g pX pY hg))
    (isDeformationCategory_schemeMorphismDeformationCategoryProjection g pX pY hg)
    (FGModuleCat.of k (ULift.{u} k))

/-- Actual source forgetting into the original dual-cotangent H1. -/
def sourceForgettingH1 :
    ↥(morphismTangentModule pX pY g hg) →ₗ[k]
      cohomologyOverField k pX (CurveTangentLineGeometry.tangentLine pX) 1 :=
  (StandardSchemeTangent.endpointTangentLinearEquivH1 (Λ := k) pX).toLinearMap.comp
    ((LinearMap.fst k _ _).comp
      (SchemeMorphismSourceObstruction.endpointTangentMap pX pY g hg))

/-- Its value is literally the source endpoint class under the original
standard H1 classifier. -/
theorem sourceForgettingH1_apply (t : ↥(morphismTangentModule pX pY g hg)) :
    sourceForgettingH1 pX pY g hg t =
      StandardSchemeTangent.endpointTangentLinearEquivH1 (Λ := k) pX
        ((SchemeMorphismSourceObstruction.endpointTangentMap pX pY g hg t).1) := by
  simp only [sourceForgettingH1, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearEquiv.coe_toLinearMap]

end M9Native.SchemeMorphismSourceH1
