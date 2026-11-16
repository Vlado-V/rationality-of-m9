module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSixTermExact

/-!
# The original endpoint tangent image satisfies the original morphism obstruction

These are the native equicharacteristic scheme-morphism deformation
category, its two actual endpoint tangent maps, and its native
Push-minus-Pull obstruction. Original exactness derives the necessary
image inclusion; no relation on the deformation image is assumed.
Identification with the literal cotangent derivative remains a separate
normalization of the actual class maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry Deformation Deformation.Examples

universe u

namespace M9Native.SchemeMorphismSourceObstruction

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
variable (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
variable (g : X ⟶ Y) (hg : g ≫ pY = pX)

/-- The literal original source-and-target forgetting tangent map. -/
abbrev endpointTangentMap :=
  schemeMorphismTangentPair' (Λ := k) g pX pY hg
    (isDeformationCategory_schemeMorphismDeformationCategoryProjection g pX pY hg)
    (FGModuleCat.of k (ULift.{u} k))

/-- The literal native Push-minus-Pull obstruction map. -/
abbrev obstructionMap := schemeMorphismObstructionLinearMap (Λ := k) g pX pY hg

/-- Original endpoint tangent vectors of a genuine morphism deformation
have zero original morphism obstruction. -/
theorem endpoint_obstruction_zero :
    letI := schemeMorphismObstructionExtModule (Λ := k) g pY
    ∀ t, obstructionMap pX pY g hg (endpointTangentMap pX pY g hg t) = 0 := by
  let := schemeMorphismObstructionExtModule (Λ := k) g pY
  intro t
  exact (exact_schemeMorphismTangentPair'_schemeMorphismObstructionLinearMap
    (Λ := k) g pX pY hg _).mpr ⟨t, rfl⟩

/-- A necessary image relation derived from the native deformation
sequence, without a supplied image or compatibility premise. -/
theorem endpoint_range_le_obstruction_kernel :
    letI := schemeMorphismObstructionExtModule (Λ := k) g pY
    LinearMap.range (endpointTangentMap pX pY g hg) ≤
      LinearMap.ker (obstructionMap pX pY g hg) := by
  let := schemeMorphismObstructionExtModule (Λ := k) g pY
  rintro x ⟨t, rfl⟩
  exact endpoint_obstruction_zero pX pY g hg t

end M9Native.SchemeMorphismSourceObstruction
