module

public import M9StacksIntegration.PrimitiveUniversalExtensionPoints
public import M9StacksIntegration.PrimitiveExtensionFieldBridge
public import M9StacksIntegration.NativeAffinePullbackEvaluation

@[expose] public section

/-! The original symplectic group over an extension field gives a point of
the actual native group scheme.  The native action is identified with the
original fourteen-coordinate primitive representation, including its
inverse-precomposition convention on quotient presentations.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace M9Native.PrimitiveOriginalExtensionAction

open PrimitiveGrassmannianAction PrimitiveUniversalExtensionPoints

variable {L : Type} [Field L] [Algebra ℂ L]

/-- The literal original symplectic transformation as a native group point. -/
def nativeGroupPoint (g : M9.PrimitiveStabilizer.Sp6 L) : overField L ⟶ group :=
  (Sp6GroupScheme.pointsMulEquiv PrimitiveFamilyFreeAction.base (overField L)).symm
    (Sp6GroupScheme.mapMatrix (Scheme.ΓSpecIso (.of L)).inv.hom
      (PrimitiveExtensionFieldBridge.fromOriginal L g))

theorem pointsMulEquiv_nativeGroupPoint (g : M9.PrimitiveStabilizer.Sp6 L) :
    Sp6GroupScheme.pointsMulEquiv PrimitiveFamilyFreeAction.base (overField L) (nativeGroupPoint g) =
      Sp6GroupScheme.mapMatrix (Scheme.ΓSpecIso (.of L)).inv.hom
        (PrimitiveExtensionFieldBridge.fromOriginal L g) :=
  (Sp6GroupScheme.pointsMulEquiv PrimitiveFamilyFreeAction.base (overField L)).apply_symm_apply _

/-- The actual global-section matrix recovers the original extension-field matrix. -/
theorem nativeGroupPoint_matrix (g : M9.PrimitiveStabilizer.Sp6 L) :
    Sp6GroupScheme.mapMatrix (Scheme.ΓSpecIso (.of L)).hom.hom
      (Sp6GroupScheme.pointsMulEquiv PrimitiveFamilyFreeAction.base (overField L) (nativeGroupPoint g)) =
        PrimitiveExtensionFieldBridge.fromOriginal L g := by
  rw [pointsMulEquiv_nativeGroupPoint]
  apply Subtype.ext
  ext i j
  exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (.of L)) _

/-- The native test scheme uses the actual original complex scalar map. -/
theorem scalarMap_spec :
    (Scheme.ΓSpecIso (.of L)).hom.hom.comp (PrimitiveFamilyFreeAction.scalarMap (overField L)) =
      algebraMap ℂ L := by
  ext c
  exact NativeAffinePullbackEvaluation.sectionValue_specMap (algebraMap ℂ L) c

/-- The free-fourteen matrix of the native action is the literal primitive
matrix of the original symplectic transformation over the extension field. -/
theorem nativeGroupPoint_familyMatrix (g : M9.PrimitiveStabilizer.Sp6 L) :
    (PrimitiveFamilyFreeAction.familyMatrix (overField L)
      (Sp6GroupScheme.pointsMulEquiv PrimitiveFamilyFreeAction.base (overField L) (nativeGroupPoint g))).map
        (Scheme.ΓSpecIso (.of L)).hom.hom =
      PrimitiveRingCoordinates.primitiveMatrix L (algebraMap ℂ L)
        (PrimitiveExtensionFieldBridge.fromOriginal L g) := by
  have hm := PrimitiveRingCoordinates.primitiveMatrix_map Γ((overField L).left, ⊤)
    (PrimitiveFamilyFreeAction.scalarMap (overField L)) (Scheme.ΓSpecIso (.of L)).hom.hom
    (Sp6GroupScheme.pointsMulEquiv PrimitiveFamilyFreeAction.base (overField L) (nativeGroupPoint g))
  rw [show LagrangianTransitivity.mapSymplectic Γ((overField L).left, ⊤)
      (Scheme.ΓSpecIso (.of L)).hom.hom
      (Sp6GroupScheme.pointsMulEquiv PrimitiveFamilyFreeAction.base (overField L) (nativeGroupPoint g)) =
        PrimitiveExtensionFieldBridge.fromOriginal L g from nativeGroupPoint_matrix g,
    scalarMap_spec] at hm
  exact hm.symm

/-- The native quotient-class action has exactly the original symplectic
matrix and the frozen inverse-precomposition convention. -/
theorem action_pointClass (g : M9.PrimitiveStabilizer.Sp6 L) (x : overField L ⟶ overSpace) :
    pointClass ((lift (nativeGroupPoint g) x ≫ nativeAction.act).left) =
      PrimitiveFamilyFreeAction.transformPoints (overField L)
        (Sp6GroupScheme.mapMatrix (Scheme.ΓSpecIso (.of L)).inv.hom
          (PrimitiveExtensionFieldBridge.fromOriginal L g)) (pointClass x.left) := by
  rw [nativeAction_act, PrimitiveGrassmannianAction.action_pointClass,
    pointsMulEquiv_nativeGroupPoint]

/-- Literal exterior coefficients identify the same primitive linear map. -/
theorem primitiveMatrix_fieldCoordinates (g : M9.PrimitiveStabilizer.Sp6 L)
    (w : M9.ExteriorPrimitive.Primitive L) :
    PrimitiveRingCoordinates.primitiveMatrix L (algebraMap ℂ L)
      (PrimitiveExtensionFieldBridge.fromOriginal L g) *ᵥ
        PrimitiveExtensionFieldBridge.fieldCoordinates L w =
      PrimitiveExtensionFieldBridge.fieldCoordinates L (M9.PrimitiveStabilizer.primitiveLinear L g w) := by
  rw [PrimitiveExtensionFieldBridge.primitiveMatrix_fieldCoordinates,
    PrimitiveExtensionFieldBridge.toOriginal_fromOriginal]

/-- The literal native family matrix acts by the original exterior representation. -/
theorem familyMatrix_fieldCoordinates (g : M9.PrimitiveStabilizer.Sp6 L)
    (w : M9.ExteriorPrimitive.Primitive L) :
    (PrimitiveFamilyFreeAction.familyMatrix (overField L)
      (Sp6GroupScheme.pointsMulEquiv PrimitiveFamilyFreeAction.base (overField L) (nativeGroupPoint g))).map
        (Scheme.ΓSpecIso (.of L)).hom.hom *ᵥ
          PrimitiveExtensionFieldBridge.fieldCoordinates L w =
      PrimitiveExtensionFieldBridge.fieldCoordinates L (M9.PrimitiveStabilizer.primitiveLinear L g w) := by
  rw [nativeGroupPoint_familyMatrix, primitiveMatrix_fieldCoordinates]

end M9Native.PrimitiveOriginalExtensionAction
