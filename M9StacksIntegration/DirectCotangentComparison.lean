module

public import M9StacksIntegration.StandardSmoothCotangentProjection
public import StacksFrontier.Deformation.RingedSpaceThickening.DerivedPullbackNaiveCotangentMap

/-!
# Naturality of the literal direct derived cotangent comparison

The original direct map uses the quotient/homotopy comparison before its
actual degreewise adjoint map. This leaf constructs that same comparison
as a natural transformation, with no replacement by a tower comparison.
The natural-transformation assembly is the thin, scheme-independent part
of pinned StacksFrontier DerivedPullbackTwoTerm, restated in a new namespace;
that unneeded full two-term dependency is not imported or altered.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry RingedSpaceModuleAdjunction
open AlgebraicGeometry.RingedSpaceThickening
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

attribute [local instance 100000] HasDerivedCategory.standard

universe u v w

namespace M9Native.DirectCotangentComparison

section Single

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The original single/homotopy comparison is the original quotient
comparison at the single complex. -/
theorem singleFunctorIsoCompQh_hom (F : C) :
    ((DerivedCategory.singleFunctorIsoCompQh C 0).hom.app F) =
      (DerivedCategory.quotientCompQhIso C).inv.app
        ((CochainComplex.singleFunctor C 0).obj F) := by
  simp [DerivedCategory.singleFunctorIsoCompQh, DerivedCategory.singleFunctorsPostcompQhIso,
    SingleFunctors.evaluation, SingleFunctors.postcompIsoOfIso,
    SingleFunctors.postcompPostcompIso, SingleFunctors.isoMk]

end Single

variable {X Y : RingedSpace.{u,u}} (g : X ⟶ Y)

/-- The genuine original comparison as a natural transformation on the
original cochain category. -/
def comparisonNat :
    DerivedCategory.Q ⋙ derivedPullback g ⟶
      (modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing Y))).inv
      (derivedPullback g) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
      (derivedPullbackComparison g) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (((modulePullback g).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).hom) DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).hom

/-- Its component retains the exact original quotient/homotopy arrows. -/
theorem comparisonNat_app (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) :
    (comparisonNat g).app K =
      (derivedPullback g).map ((DerivedCategory.quotientCompQhIso _).inv.app K) ≫
        (derivedPullbackComparison g).app ((HomotopyCategory.quotient _ _).obj K) ≫
        (DerivedCategory.quotientCompQhIso _).hom.app
          (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  have h : ((modulePullback g).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app K =
      𝟙 ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)).obj
          (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := rfl
  have hi := (congrArg DerivedCategory.Qh.map h).trans (DerivedCategory.Qh.map_id _)
  simp only [comparisonNat, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app]
  rw [hi]
  simp only [Category.id_comp]
  exact congrArg
    (fun t : DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ)).obj
            (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ⟶
        DerivedCategory.Q.obj
          (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =>
      (derivedPullback g).map
        ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing Y))).inv.app K) ≫
      (derivedPullbackComparison g).app
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
          (ComplexShape.up ℤ)).obj K) ≫ t)
    (Category.id_comp
      ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing X))).hom.app
        (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))

/-- Naturality of the exact original direct comparison. -/
@[reassoc]
theorem comparison_naturality {K L : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ}
    (a : K ⟶ L) :
    (derivedPullback g).map (DerivedCategory.Q.map a) ≫ (comparisonNat g).app L =
      (comparisonNat g).app K ≫ DerivedCategory.Q.map
        (((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map a) :=
  (comparisonNat g).naturality a

/-- The actual direct cotangent arrow factors through this literal
comparison and its actual canonical-presentation adjoint. -/
theorem directMap_eq {S : RingedSpace.{u,u}} (f : Y ⟶ S) :
    derivedPullbackNaiveCotangentMap g f =
      (comparisonNat g).app
        (show CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ from
          PresentedSquareZeroExtension.relativeComplex f) ≫
        DerivedCategory.Q.map (pullbackNaiveCotangentMap g f) := by
  rw [comparisonNat_app]
  dsimp only [derivedPullbackNaiveCotangentMap]
  simp only [Category.assoc, HomotopyCategory.quotient_obj_as]

/-- On an original single complex this is the exact single-pullback
comparison used by the original coefficient and smooth-normalization maps. -/
@[reassoc]
theorem comparison_single (F : SheafOfModules.{u} (structureSheafRing Y)) :
    (comparisonNat g).app ((CochainComplex.singleFunctor (SheafOfModules.{u} (structureSheafRing Y)) 0).obj F) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex (modulePullback g)
          (ComplexShape.up ℤ) 0).hom.app F) =
      derivedPullbackSingleObj g F := by
  rw [comparisonNat_app]
  dsimp only [derivedPullbackSingleObj]
  rw [singleFunctorIsoCompQh_hom]
  simp only [Category.assoc]

end M9Native.DirectCotangentComparison
