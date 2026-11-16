module

public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine

/-!
# A genuine sheaf map to the unit, read in the structure-ring carrier

The source sheaf remains abstract. The target's unit-sheaf scalar
action is normalized once to the actual structure-ring action.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Opposite

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  SheafOfModules.unit PresheafOfModules.unit AlgebraicGeometry.SheafedSpace.sheaf

universe u
namespace M9Native.UnitSectionsLinearMap

/-- Actual global sections of an actual sheaf map to the unit,
with the literal structure-ring target and its regular module. -/
def toRing {X : Scheme.{u}} (F : X.Modules)
    (φ : F ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :
    Γ(F,⊤) →ₗ[Γ(X,⊤)] Γ(X,⊤) where
  toFun := φ.app ⊤
  map_add' a b := (φ.val.app (op ⊤)).hom.map_add a b
  map_smul' r s := by
    change φ.app ⊤ (r • s) = r • φ.app ⊤ s
    exact Scheme.Modules.Hom.app_smul φ r s

theorem toRing_apply {X : Scheme.{u}} (F : X.Modules)
    (φ : F ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) (s : Γ(F,⊤)) :
    toRing F φ s = (show Γ(X,⊤) from φ.app ⊤ s) := rfl

end M9Native.UnitSectionsLinearMap
