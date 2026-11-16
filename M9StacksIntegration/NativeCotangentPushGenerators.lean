module

public import StacksFrontier.Deformation.RingedSpaceThickening.DerivedPullbackNaiveCotangentMap
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentCokernelDerivation

/-!
# The actual direct cotangent push-map on original universal generators

This is the direct canonical-presentation map used by the native
compatible-morphism derived class construction. The degree-zero action
is computed from the actual presentation tensor map and the actual free
algebra variable map. The separate tower-based comparison is not used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.RingedSpaceThickening
open Stacks.SheafOfModules Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal

universe u

namespace M9Native.NativeCotangentPushGenerators

variable {X Y S : RingedSpace.{u,u}} (g : X ⟶ Y) (f : Y ⟶ S)

/-- The actual degree-zero variable differential in the original complex. -/
abbrev variableDifferential (U : (Opens Y.carrier)ᵒᵖ) (b : Y.sheaf.obj.obj U) :=
  naiveCotangentVariableDifferential.{u,u,u,u} (Opens.grothendieckTopology Y.carrier)
    (inverseImageBaseRing f) Y.sheaf (structureRingMap f) U b

/-- The direct actual push-map sends the variable differential of b to
that of its literal structure-comorphism image. -/
theorem pushMap_variableDifferential (U : (Opens Y.carrier)ᵒᵖ)
    (b : Y.sheaf.obj.obj U) :
    ((naiveCotangentPushMap g f).f 0).val.app U (variableDifferential f U b) =
      variableDifferential (g ≫ f) ((Opens.map g.hom.base).op.obj U)
        ((structureComorphism g).hom.app U b) := by
  have hv := congrArg (fun t => t.app U b)
    (freeAlgebraSheafVariable_comp_freeAlgebraPushMap g.hom.base
      (inverseImageBaseRing f)
      (underlyingPresheaf (Opens.grothendieckTopology Y.carrier) Y.sheaf)
      (inverseImageBaseRing (g ≫ f))
      (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf)
      (baseRingPushMap g f)
      (Functor.whiskerRight (structureComorphism g).hom (forget CommRingCat.{u})))
  change (sectionsMapAlong g.hom.base
      (freeAlgebraPushMap g.hom.base (inverseImageBaseRing f)
        (underlyingPresheaf (Opens.grothendieckTopology Y.carrier) Y.sheaf)
        (inverseImageBaseRing (g ≫ f))
        (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf)
        (baseRingPushMap g f)
        (Functor.whiskerRight (structureComorphism g).hom (forget CommRingCat.{u}))) U).hom
      (variableSection (Opens.grothendieckTopology Y.carrier)
        (inverseImageBaseRing f) Y.sheaf U b) =
    variableSection (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing (g ≫ f)) X.sheaf ((Opens.map g.hom.base).op.obj U)
      ((structureComorphism g).hom.app U b) at hv
  dsimp only [naiveCotangentPushMap]
  rw [presentationNaiveCotangentPushMap_f_zero]
  dsimp only [variableDifferential, naiveCotangentVariableDifferential]
  refine (eqToHom_comp_val_app_eqToHom_symm _ _ U _).trans ?_
  dsimp only [presentationTensorPushMap]
  refine congrArg (fun t =>
    (eqToHom (naiveCotangentComplex_X_zero.{u,u,u,u}
      (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing (g ≫ f))
      X.sheaf (structureRingMap (g ≫ f))).symm).val.app
        ((Opens.map g.hom.base).op.obj U) t) ?_
  refine (tensorSheafMapPush_tensorDifferential g.hom.base Y.sheaf X.sheaf
    (structureComorphism g) _ _ _
    (freeAlgebraPushMap_comp_presentation g.hom.base
      (structureRingMap_comp_structureComorphism g f) (underlyingPresheafMap_comp g))
    _ _ _ _ (baseRingPushMap g f) (freeAlgebraPushMap_coefficient g.hom.base) U _).trans ?_
  exact congrArg (fun s => tensorDifferential.{u,u,u,u}
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing (g ≫ f))
    (freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing (g ≫ f))
      (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf)) X.sheaf
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing (g ≫ f))
      (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf))
    (canonicalPresentation (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing (g ≫ f)) X.sheaf (structureRingMap (g ≫ f)))
    ((Opens.map g.hom.base).op.obj U) s) hv

end M9Native.NativeCotangentPushGenerators
