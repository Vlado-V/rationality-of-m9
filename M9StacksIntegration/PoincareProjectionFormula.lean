module

public import M9StacksIntegration.PoincarePicardTensor
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaInvertible.Basic

/-!
# The actual ordinary projection formula with an invertible base line

This transports the unconditional native projection formula to the
actual `Scheme.Modules` tensor product and pullback used by the
Poincare ordinary direct-image construction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace M9Native.PoincareChern

/-- The ordinary projection formula for an actual invertible base
line, with no hypothesis on the actual morphism or upstairs module. -/
def invertibleOrdinaryProjectionFormulaIso
    {Y S : Scheme.{u}} (π : Y ⟶ S) (L : Y.Modules) (N : S.Modules)
    [hN : Stacks.SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N] :
    Scheme.Modules.tensorObj ((Scheme.Modules.pushforward π).obj L) N ≅
      (Scheme.Modules.pushforward π).obj
        (Scheme.Modules.tensorObj L ((Scheme.Modules.pullback π).obj N)) := by
  letI : Stacks.SheafOfModules.IsInvertible S.toRingedSpace.sheaf.obj
      (Stacks.RingedSpace.structureRingSheaf S.toRingedSpace).property N := hN
  exact Stacks.ProjectionFormula.projectionFormulaIso π.toLRSHom.toShHom L N ≪≫
    (Scheme.Modules.pushforward π).mapIso
      (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).obj L).mapIso
        ((Stacks.ProjectiveBundleQuotients.pullbackIso π).app N).symm)

end M9Native.PoincareChern
