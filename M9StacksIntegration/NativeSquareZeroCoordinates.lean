module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationCoordinateIdeal
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Defs

/-!
# Coordinates on the original native square-zero base

The native deformation base uses the named central right action on a
module. Dual-number tangent arrows use the ordinary right multiplication
on the field. The identity on both coordinates is a genuine ring
isomorphism between these presentations, with naturality proved below.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory Deformation Deformation.Examples

universe u

namespace M9Native.NativeSquareZeroCoordinates

variable (k : Type u) [Field k]

/-- Actual coordinates, including the original native right scalar action. -/
def ringEquiv (V : FGModuleCat.{u} k) [Module kᵐᵒᵖ V] [IsCentralScalar k V] :
    (coordBase (Λ := k) V : Type u) ≃+* TrivSqZeroExt k V where
  toFun z := ⟨z.fst, z.snd⟩
  invFun z := ⟨z.fst, z.snd⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · rfl
    · change a.fst • b.snd + b.fst • a.snd =
        a.fst • b.snd + (MulOpposite.op b.fst) • a.snd
      rw [op_smul_eq_smul]

/-- Taking spectra gives the actual coordinate map from the native base. -/
def toSpec (V : FGModuleCat.{u} k) [Module kᵐᵒᵖ V] [IsCentralScalar k V] :
    baseSpec (coordBase (Λ := k) V) ⟶ Spec (.of (TrivSqZeroExt k V)) :=
  Spec.map (CommRingCat.ofHom (ringEquiv k V).symm.toRingHom)

/-- The coordinate map is an actual scheme isomorphism. -/
instance toSpec_isIso (V : FGModuleCat.{u} k) [Module kᵐᵒᵖ V]
    [IsCentralScalar k V] : IsIso (toSpec k V) := by
  have := (ringEquiv k V).symm.toCommRingCatIso.isIso_hom
  exact inferInstanceAs (IsIso (Spec.map (ringEquiv k V).symm.toCommRingCatIso.hom))

/-- The original closed point is the ordinary square-zero first projection. -/
theorem residue_toSpec (V : FGModuleCat.{u} k) [Module kᵐᵒᵖ V]
    [IsCentralScalar k V] :
    residueSpecMap (coordBase (Λ := k) V) ≫ toSpec k V =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k V).toRingHom) := by
  rw [toSpec, ← Spec.map_comp]
  congr 1

/-- The actual coordinate map is natural for every genuine finite-coefficient map. -/
theorem toSpec_naturality {V W : FGModuleCat.{u} k}
    [Module kᵐᵒᵖ V] [IsCentralScalar k V]
    [Module kᵐᵒᵖ W] [IsCentralScalar k W] (g : V ⟶ W) :
    baseSpecMap ((squareZeroExtensionArtinian k k).map g) ≫ toSpec k V =
      toSpec k W ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map g.hom.hom).toRingHom) := by
  rw [toSpec, toSpec, ← Spec.map_comp, ← Spec.map_comp]
  congr 1

end M9Native.NativeSquareZeroCoordinates
