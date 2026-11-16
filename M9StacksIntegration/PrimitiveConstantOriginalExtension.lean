module

public import M9StacksIntegration.PrimitiveFieldMatrixAction
public import M9StacksIntegration.PrimitiveConstantFieldAction

@[expose] public section

/-! Original constant symplectic transformations retain the identical actual
native group point after extension of coefficients. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped Classical CategoryTheory.MonObj

namespace M9Native.PrimitiveConstantOriginalExtension
open PrimitiveGrassmannianAction PrimitiveUniversalExtensionPoints

variable (K : Type) [Field K] [Algebra ℂ K]

/-- Literal scalar extension of the original complex symplectic matrix,
returned in the original exterior-model group over the extension field. -/
def extendConstant (g : PrimitiveConstantFieldAction.Sp6) : M9.PrimitiveStabilizer.Sp6 K :=
  PrimitiveExtensionFieldBridge.toOriginal K
    (Sp6GroupScheme.mapMatrix (algebraMap ℂ K) (PrimitiveRingFieldBridge.fromOriginal g))

theorem scalarMap_spec_inverse : PrimitiveFamilyFreeAction.scalarMap (overField K) =
    (Scheme.ΓSpecIso (.of K)).inv.hom.comp (algebraMap ℂ K) := by
  ext c
  apply (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.injective
  change (Scheme.ΓSpecIso (.of K)).hom _ =
    (Scheme.ΓSpecIso (.of K)).hom ((Scheme.ΓSpecIso (.of K)).inv (algebraMap ℂ K c))
  rw [Iso.inv_hom_id_apply]
  exact DFunLike.congr_fun (PrimitiveOriginalExtensionAction.scalarMap_spec (L := K)) c

/-- The two genuine native group points coincide, before acting on any Grassmannian. -/
theorem nativeGroupPoint_extendConstant (g : PrimitiveConstantFieldAction.Sp6) :
    PrimitiveOriginalExtensionAction.nativeGroupPoint (extendConstant K g) =
      PrimitiveFamilyFreeAction.constantPointOn (overField K) g := by
  apply (Sp6GroupScheme.pointsMulEquiv PrimitiveFamilyFreeAction.base (overField K)).injective
  rw [PrimitiveOriginalExtensionAction.pointsMulEquiv_nativeGroupPoint,
    PrimitiveFamilyFreeAction.pointsMulEquiv_constantPointOn,
    extendConstant,PrimitiveExtensionFieldBridge.fromOriginal_toOriginal]
  apply Subtype.ext
  ext i j
  change (Scheme.ΓSpecIso (.of K)).inv (algebraMap ℂ K _) =
    PrimitiveFamilyFreeAction.scalarMap (overField K) _
  rw [scalarMap_spec_inverse]
  rfl

/-- Extension of the original group element gives the literal original
constant native scheme action, with its original composition convention. -/
theorem actPoint_extendConstant (g : PrimitiveConstantFieldAction.Sp6)
    (p : Spec (.of K) ⟶ space)
    (hp : p ≫ projection = Spec.map (CommRingCat.ofHom (algebraMap ℂ K))) :
    PrimitiveFieldMatrixAction.actPoint K (extendConstant K g) p hp =
      p ≫ PrimitiveConstantFieldAction.schemeMap g := by
  change (lift (PrimitiveOriginalExtensionAction.nativeGroupPoint (extendConstant K g))
    (PrimitiveFieldMatrixAction.overPoint K p hp) ≫ nativeAction.act).left =
      ((PrimitiveFieldMatrixAction.overPoint K p hp) ≫ PrimitiveConstantFieldAction.overMap g).left
  rw [nativeGroupPoint_extendConstant,PrimitiveConstantFieldAction.overMap_comp]

end M9Native.PrimitiveConstantOriginalExtension
