module

public import M9StacksIntegration.SchemeRawDifferenceClass
public import M9StacksIntegration.SolutionThickenedSheafMapAlong
public import M9StacksIntegration.RawCompatibleMorphismOperations
public import M9StacksIntegration.ExtensionIdealMapAlong
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismEndpoints
public import StacksFrontier.Deformation.RingedSpaceThickening.CompatibleMorphismPresentation

/-! Actual coordinate endpoint extensions of a scheme-morphism family,
with the original pulled-ideal coefficients retained. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Deformation Deformation.Examples RingedSpaceModuleAdjunction
open AlgebraicGeometry.RingedSpaceThickening

universe u

namespace M9Native.SchemeRawCompatibleMorphism

section Rebase

variable {X S : RingedSpace.{u,u}} {f f' : X ⟶ S}
  {G : SheafOfModules.{u} (structureSheafRing X)}

theorem rebase_idealBijective (h : f = f') (P : AlgebraSquareZeroExtension f G)
    (hP : P.IdealBijective) :
    (SchemeRawDifferenceClass.rebaseExtension h P).IdealBijective := by
  subst f'
  exact hP

def rebaseSquare (h : f = f') (P : SquareZeroAlgebraExtension f G) :
    SquareZeroAlgebraExtension f' G := h ▸ P

theorem rebaseSquare_toAlgebra (h : f = f') (P : SquareZeroAlgebraExtension f G) :
    (rebaseSquare h P).toAlgebraSquareZeroExtension =
      SchemeRawDifferenceClass.rebaseExtension h P.toAlgebraSquareZeroExtension := by
  subst f'
  rfl

end Rebase

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The frozen raw extension with its genuine sectionwise exactness. -/
def rawSquare (Z : Over (Spec (.of k))) (V : FGModuleCat.{u} k)
    (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z).Fiber (coordBase V)) :
    SquareZeroAlgebraExtension Z.hom.toLRSHom.toShHom
      (SchemeDeformationCategory.pulledIdeal (coordBase (Λ := Λ) V) Z) where
  toAlgebraSquareZeroExtension := SchemeRawDifferenceClass.rawFiberExtension Z V x
  ideal_bijective := rebase_idealBijective
    (SchemeRawDifferenceClass.retraction_comp (f := Z.hom.toLRSHom.toShHom)
      (SchemeRawDifferenceClass.closedMap V) (SchemeRawDifferenceClass.baseProjection V)
      (SchemeRawDifferenceClass.base_retraction V))
    ((SchemeRawDifferenceClass.coordinateSolution Z V x).toAlgebraExtension.restrictBase
      (SchemeRawDifferenceClass.baseProjection V))
    (SchemeRawDifferenceClass.coordinateSolution Z V x).toAlgebraExtension_idealBijective

theorem rawSquare_toAlgebra (Z : Over (Spec (.of k))) (V : FGModuleCat.{u} k)
    (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z).Fiber (coordBase V)) :
    (rawSquare Z V x).toAlgebraSquareZeroExtension =
      SchemeRawDifferenceClass.rawFiberExtension Z V x := rfl

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k))
  (pY : Y ⟶ baseSpec (residueFieldBase Λ k)) (hg : g ≫ pY = pX)
  (V : FGModuleCat.{u} k)

abbrev FamilyFiber :=
  (schemeMorphismDeformationCategoryProjection (Λ := Λ) (k := k) g pX pY hg).Fiber
    (coordBase V)

variable (x : FamilyFiber g pX pY hg V)

/-- Both endpoint fibres use the actual same coordinate base equality. -/
def sourceFiber :
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).Fiber
      (coordBase V) :=
  ⟨(schemeMorphismSourceForgetful g pX pY hg).obj x.1, x.2⟩

def targetFiber :
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
      (coordBase V) :=
  ⟨(schemeMorphismTargetForgetful g pX pY hg).obj x.1, x.2⟩

/-- The source is exactly the native fiberFunctor image of the family. -/
theorem sourceFiber_eq_fiberFunctor : sourceFiber g pX pY hg V x =
    (fiberFunctor (schemeMorphismSourceBased g pX pY hg) (coordBase V)).obj x := by
  apply Subtype.ext
  rfl

/-- The target is exactly the native fiberFunctor image of the family. -/
theorem targetFiber_eq_fiberFunctor : targetFiber g pX pY hg V x =
    (fiberFunctor (schemeMorphismTargetBased g pX pY hg) (coordBase V)).obj x := by
  apply Subtype.ext
  rfl

abbrev sourceSolution :=
  SchemeRawDifferenceClass.coordinateSolution (Over.mk pX) V (sourceFiber g pX pY hg V x)

abbrev targetSolution :=
  SchemeRawDifferenceClass.coordinateSolution (Over.mk pY) V (targetFiber g pX pY hg V x)

abbrev totalMap : (sourceSolution g pX pY hg V x).X' ⟶
    (targetSolution g pX pY hg V x).X' :=
  x.1.left.morphism.toLRSHom.toShHom

/-- The original special-fibre square of the actual family. -/
theorem special_square : (sourceSolution g pX pY hg V x).i ≫ totalMap g pX pY hg V x =
    g.toLRSHom.toShHom ≫ (targetSolution g pX pY hg V x).i := by
  exact congrArg (fun m : X ⟶ x.1.left.target => m.toLRSHom.toShHom)
    x.1.hom.source_pullback.w.symm

/-- The original deformed map is over the actual coordinate base. -/
theorem coordinate_base_square :
    totalMap g pX pY hg V x ≫ (targetSolution g pX pY hg V x).f' =
      (sourceSolution g pX pY hg V x).f' := by
  have h : x.1.left.morphism ≫
      (x.1.left.targetToBase ≫ eqToHom (congrArg baseSpec x.2)) =
      x.1.left.sourceToBase ≫ eqToHom (congrArg baseSpec x.2) := by
    rw [← Category.assoc, x.1.left.over_base]
  exact congrArg (fun m : x.1.left.source ⟶ baseSpec (coordBase (Λ := Λ) V) =>
    m.toLRSHom.toShHom) h

include hg in
/-- Only the original structure-map equality rebases the raw source. -/
theorem original_square : pX.toLRSHom.toShHom =
    g.toLRSHom.toShHom ≫ pY.toLRSHom.toShHom :=
  congrArg (fun m : X ⟶ baseSpec (residueFieldBase Λ k) => m.toLRSHom.toShHom) hg.symm

def targetExtension :=
  rawSquare (Over.mk pY) V (targetFiber g pX pY hg V x)

def sourceExtension :=
  rebaseSquare (original_square g pX pY hg)
    (rawSquare (Over.mk pX) V (sourceFiber g pX pY hg V x))

theorem targetExtension_toAlgebra :
    (targetExtension g pX pY hg V x).toAlgebraSquareZeroExtension =
      SchemeRawDifferenceClass.rawFiberExtension (Over.mk pY) V
        (targetFiber g pX pY hg V x) := rfl

theorem sourceExtension_toAlgebra :
    (sourceExtension g pX pY hg V x).toAlgebraSquareZeroExtension =
      SchemeRawDifferenceClass.rebaseExtension (original_square g pX pY hg)
        (SchemeRawDifferenceClass.rawFiberExtension (Over.mk pX) V
          (sourceFiber g pX pY hg V x)) :=
  rebaseSquare_toAlgebra _ _

/-- The actual map of original thickened structure sheaves. -/
abbrev originalSheafMap := SolutionThickenedSheafMapAlong.sheafMap
  (targetSolution g pX pY hg V x) (sourceSolution g pX pY hg V x) g.toLRSHom.toShHom
  (totalMap g pX pY hg V x) (special_square g pX pY hg V x)

section Literal

variable (z : FamilyFiber g (g ≫ pY) pY rfl V)

abbrev literalTargetSolution := targetSolution g (g ≫ pY) pY rfl V z
abbrev literalSourceSolution := sourceSolution g (g ≫ pY) pY rfl V z

/-- The genuine target extension before restricting its base. -/
def coordinateTargetExtension :
    SquareZeroAlgebraExtension
      (pY.toLRSHom.toShHom ≫ SchemeRawDifferenceClass.closedMap (Λ := Λ) V)
      (SchemeDeformationCategory.pulledIdeal (coordBase (Λ := Λ) V) (Over.mk pY)) where
  toAlgebraSquareZeroExtension := (literalTargetSolution g pY V z).toAlgebraExtension
  ideal_bijective := (literalTargetSolution g pY V z).toAlgebraExtension_idealBijective

/-- The genuine source extension before restricting its base. -/
def coordinateSourceExtension :
    SquareZeroAlgebraExtension
      (g.toLRSHom.toShHom ≫
        (pY.toLRSHom.toShHom ≫ SchemeRawDifferenceClass.closedMap (Λ := Λ) V))
      (SchemeDeformationCategory.pulledIdeal (coordBase (Λ := Λ) V) (Over.mk (g ≫ pY))) where
  toAlgebraSquareZeroExtension := (literalSourceSolution g pY V z).toAlgebraExtension
  ideal_bijective := (literalSourceSolution g pY V z).toAlgebraExtension_idealBijective

abbrev literalSheafMap := originalSheafMap g (g ≫ pY) pY rfl V z

/-- The actual ideal map induced by the original deformed map. -/
def literalCoefficientMap := ExtensionIdealMapAlong.coefficientMap
  (coordinateTargetExtension g pY V z) (coordinateSourceExtension g pY V z)
  g.toLRSHom.toShHom (literalSheafMap g pY V z)
  (SolutionThickenedSheafMapAlong.sheafMap_comp_reduction
    (literalTargetSolution g pY V z) (literalSourceSolution g pY V z) g.toLRSHom.toShHom
    (totalMap g (g ≫ pY) pY rfl V z) (special_square g (g ≫ pY) pY rfl V z))

/-- The actual compatible morphism over the square-zero coordinate base. -/
def coordinateCompatible : CompatibleMorphism (coordinateTargetExtension g pY V z)
    (coordinateSourceExtension g pY V z) (literalCoefficientMap g pY V z) where
  hom := literalSheafMap g pY V z
  reduction_comm := SolutionThickenedSheafMapAlong.sheafMap_comp_reduction
    (literalTargetSolution g pY V z) (literalSourceSolution g pY V z) g.toLRSHom.toShHom
    (totalMap g (g ≫ pY) pY rfl V z) (special_square g (g ≫ pY) pY rfl V z)
  base_comm := by
    change (literalTargetSolution g pY V z).toAlgebraExtension.adjointBase ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u}
        (pY.toLRSHom.toShHom ≫ SchemeRawDifferenceClass.closedMap (Λ := Λ) V).hom.base).map
        (literalSheafMap g pY V z) =
      (literalSourceSolution g pY V z).toAlgebraExtension.adjointBase
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    have ho := SolutionThickenedSheafMapAlong.over_square
      (literalTargetSolution g pY V z) (literalSourceSolution g pY V z) g.toLRSHom.toShHom
      (totalMap g (g ≫ pY) pY rfl V z) (special_square g (g ≫ pY) pY rfl V z)
      (coordinate_base_square g (g ≫ pY) pY rfl V z)
    have h := SheafedSpace.congr_hom_app ho U
    change (literalTargetSolution g pY V z).toAlgebraExtension.adjointBase.hom.app U ≫
      (literalSheafMap g pY V z).hom.app
        ((Opens.map (pY.toLRSHom.toShHom ≫
          SchemeRawDifferenceClass.closedMap (Λ := Λ) V).hom.base).op.obj U) =
      (literalSourceSolution g pY V z).toAlgebraExtension.adjointBase.hom.app U
    change (literalTargetSolution g pY V z).toAlgebraExtension.adjointBase.hom.app U ≫
      (literalSheafMap g pY V z).hom.app
        ((Opens.map (pY.toLRSHom.toShHom ≫
          SchemeRawDifferenceClass.closedMap (Λ := Λ) V).hom.base).op.obj U) =
      (literalSourceSolution g pY V z).toAlgebraExtension.adjointBase.hom.app U ≫
        (literalSourceSolution g pY V z).thickenedPresheaf.map (𝟙 _) at h
    rw [(literalSourceSolution g pY V z).thickenedPresheaf.map_id] at h
    exact h.trans (Category.comp_id _)
  ideal_comm U n := ExtensionIdealMapAlong.incl_comm _ _ _ _ _ (op U) n

abbrev literalRebase :
    (pY.toLRSHom.toShHom ≫ SchemeRawDifferenceClass.closedMap (Λ := Λ) V) ≫
        SchemeRawDifferenceClass.baseProjection (Λ := Λ) V = pY.toLRSHom.toShHom :=
  SchemeRawDifferenceClass.retraction_comp (SchemeRawDifferenceClass.closedMap V)
    (SchemeRawDifferenceClass.baseProjection V) (SchemeRawDifferenceClass.base_retraction V)

/-- The actual target extension after forgetting the square-zero base. -/
def literalTargetExtension := RawCompatibleMorphismOperations.rebased (literalRebase pY V)
  (RawCompatibleMorphismOperations.restricted (SchemeRawDifferenceClass.baseProjection V)
    (coordinateTargetExtension g pY V z))

/-- The actual source extension after forgetting the same base. -/
def literalSourceExtension := RawCompatibleMorphismOperations.rebased
  (congrArg (fun q => g.toLRSHom.toShHom ≫ q) (literalRebase pY V))
  (RawCompatibleMorphismOperations.restricted (SchemeRawDifferenceClass.baseProjection V)
    (coordinateSourceExtension g pY V z))

/-- These are the exact frozen raw target objects, with their original coefficients. -/
theorem literalTargetExtension_toAlgebra :
    (literalTargetExtension g pY V z).toAlgebraSquareZeroExtension =
      SchemeRawDifferenceClass.rawFiberExtension (Over.mk pY) V
        (targetFiber g (g ≫ pY) pY rfl V z) :=
  rebaseSquare_toAlgebra _ _

/-- These are the exact frozen raw source objects, with their original coefficients. -/
theorem literalSourceExtension_toAlgebra :
    (literalSourceExtension g pY V z).toAlgebraSquareZeroExtension =
      SchemeRawDifferenceClass.rawFiberExtension (Over.mk (g ≫ pY)) V
        (sourceFiber g (g ≫ pY) pY rfl V z) :=
  rebaseSquare_toAlgebra _ _

/-- A genuine original-coefficient compatible morphism of the raw k-extensions. -/
def compatibleLiteral : CompatibleMorphism (literalTargetExtension g pY V z)
    (literalSourceExtension g pY V z) (literalCoefficientMap g pY V z) :=
  RawCompatibleMorphismOperations.rebaseCompatible (literalRebase pY V)
    (RawCompatibleMorphismOperations.restrictCompatible (SchemeRawDifferenceClass.baseProjection V)
      (coordinateCompatible g pY V z))

end Literal

end M9Native.SchemeRawCompatibleMorphism
