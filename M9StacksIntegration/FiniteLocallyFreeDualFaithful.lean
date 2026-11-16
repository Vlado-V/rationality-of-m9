module

public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFreeReflexive
public import StacksFrontier.AlgebraicGeometry.Reflexive.DualMap

/-!
# Actual sheaf duality detects maps into a finite locally free sheaf

The genuine native evaluation map into the double dual is an isomorphism.
Its naturality proves faithfulness on morphisms; in particular dualizing
an actual nonzero differential remains nonzero. There is no supplied
faithfulness or nonvanishing hypothesis for the dual map.

The short additivity calculation follows the pinned StacksFrontier
`Modules.DualBiproduct` proof, with package sources unchanged.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.FiniteLocallyFreeDualFaithful

variable {X : Scheme.{u}}

/-- Actual native dual maps are additive. -/
theorem dualMap_add (F G : X.Modules) (f g : F ⟶ G) :
    Stacks.AlgebraicGeometry.ReflexiveModules.dualMap (f + g) =
      Stacks.AlgebraicGeometry.ReflexiveModules.dualMap f +
      Stacks.AlgebraicGeometry.ReflexiveModules.dualMap g := by
  refine hom_ext_dualSheaf fun U x W y => ?_
  simp only [dualPairing_dualMap, Scheme.Modules.Hom.add_app]
  change _ = dualPairing _ (Scheme.Modules.Hom.app (dualMap f) U x
      + Scheme.Modules.Hom.app (dualMap g) U x) W y
  change _ = dualPairing _ (Scheme.Modules.Hom.app (dualMap f) U x) W y
      + dualPairing _ (Scheme.Modules.Hom.app (dualMap g) U x) W y
  simp only [dualPairing_dualMap]
  exact map_add _ _ _

/-- The literal native dual of zero is zero. -/
theorem dualMap_zero (F G : X.Modules) :
    Stacks.AlgebraicGeometry.ReflexiveModules.dualMap (0 : F ⟶ G) = 0 := by
  have h : dualMap (0 : F ⟶ G) + (0 : dualSheaf G ⟶ dualSheaf F)
      = dualMap (0 : F ⟶ G) + dualMap (0 : F ⟶ G) := by
    rw [← dualMap_add F G, add_zero, add_zero]
  exact (add_left_cancel h).symm

/-- Genuine double-dual evaluation detects all original morphisms. -/
theorem dualMap_injective (F G : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u,u,u} (R := X.ringCatSheaf) G] :
    Function.Injective (Stacks.AlgebraicGeometry.ReflexiveModules.dualMap :
      (F ⟶ G) → (dualSheaf G ⟶ dualSheaf F)) := by
  let := isIso_toDoubleDual_of_isFiniteLocallyFree G
  intro f g h
  apply (cancel_mono (toDoubleDual G)).mp
  rw [toDoubleDual_naturality f, toDoubleDual_naturality g]
  exact congrArg (fun z => toDoubleDual F ≫ dualMap z) h

/-- Dualizing an actual nonzero map into a finite locally free sheaf
preserves nonvanishing. -/
theorem dualMap_ne_zero {F G : X.Modules}
    [SheafOfModules.IsFiniteLocallyFree.{u,u,u} (R := X.ringCatSheaf) G]
    (φ : F ⟶ G) (hφ : φ ≠ 0) :
    Stacks.AlgebraicGeometry.ReflexiveModules.dualMap φ ≠ 0 := by
  intro h
  exact hφ (dualMap_injective F G (h.trans (dualMap_zero F G).symm))

end M9Native.FiniteLocallyFreeDualFaithful
