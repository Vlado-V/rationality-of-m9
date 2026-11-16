module

public import M9StacksIntegration.ParameterFamilyDeformation
public import M9StacksIntegration.NativeSquareZeroCoordinates
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Defs
public import StacksFrontier.Deformation.Applications.TangentClassCoordinateMap

/-!
# Canonical tangent arrows give actual first-order family classes

Every class here comes from the literal pullback of the original family.
The coefficient field is the original parameter residue field. The
unlifted and lifted square-zero models are related by the actual native
rank-one coefficient isomorphism, rather than by an assigned tangent map.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Deformation
open Deformation.Examples

universe u

namespace M9Native.ParameterTangentDeformation

variable {X T S : Scheme.{u}} (p : X ⟶ T) [Flat p] (s : T ⟶ S) (x : T)

local notation "κ" => IsLocalRing.ResidueField (T.presheaf.stalk x)

local instance residueTangentModule : Module κ (DottedTangentArrow s x) :=
  inferInstanceAs (Module (T.residueField x) (DottedTangentArrow s x))

/-- The fixed original fibre, over its actual parameter residue field. -/
def fibre : Over (Spec (.of κ)) :=
  ParameterFamilyDeformation.fibre (k := κ) p (T.fromSpecResidueField x)

/-- A pointed square-zero parameter test with arbitrary finite coefficients. -/
def PointedArrow (V : FGModuleCat.{u} κ) :=
  {a : baseSpec (coordBase (Λ := κ) V) ⟶ T //
    residueSpecMap (coordBase (Λ := κ) V) ≫ a =
      T.fromSpecResidueField x}

/-- The actual family pullback, as an object of the native deformation fibre. -/
def coordinateObject (V : FGModuleCat.{u} κ)
    (a : PointedArrow x V) :
    (schemeDeformationCategoryProjection (Λ := κ)
      (fibre p x)).Fiber (coordBase V) :=
  ParameterFamilyDeformation.fibreObject p (T.fromSpecResidueField x)
    (coordBase V) a.val a.property

/-- The original native class of that actual family pullback. -/
def coordinateClass (V : FGModuleCat.{u} κ)
    (a : PointedArrow x V) :
    ↥(tangentModuleAt
      (schemeDeformationBased (Λ := κ) (fibre p x))
      (isDeformationCategory_schemeDeformationCategoryProjection (fibre p x)) V) :=
  tangentClassAt
    (schemeDeformationBased (Λ := κ) (fibre p x))
    (isDeformationCategory_schemeDeformationCategoryProjection (fibre p x)) V
    (coordinateObject p x V a)

/-- The coefficient change is a genuine native cartesian deformation arrow. -/
def coordinateChange {V W : FGModuleCat.{u} κ}
    (g : V ⟶ W) (a : PointedArrow x V) (b : PointedArrow x W)
    (hg : baseSpecMap ((squareZeroExtensionArtinian κ
      κ).map g) ≫ a.val = b.val) :
    (coordinateObject p x V a).val ⟶ (coordinateObject p x W b).val :=
  ParameterFamilyDeformation.changeTest p (T.fromSpecResidueField x)
    a.val a.property b.val b.property
    ((squareZeroExtensionArtinian κ κ).map g) hg

/-- This actual cartesian arrow lies over exactly the original coefficient map. -/
theorem coordinateChange_isHomLift {V W : FGModuleCat.{u} κ}
    (g : V ⟶ W) (a : PointedArrow x V) (b : PointedArrow x W)
    (hg : baseSpecMap ((squareZeroExtensionArtinian κ κ).map g) ≫ a.val = b.val) :
    (schemeDeformationCategoryProjection (Λ := κ) (k := κ) (fibre p x)).IsHomLift
      ((squareZeroExtensionArtinian κ κ).map g)
      (coordinateChange p x g a b hg) := by
  exact Functor.IsHomLift.map
    (p := schemeDeformationCategoryProjection (Λ := κ) (k := κ) (fibre p x))
    (coordinateChange p x g a b hg)

/-- Naturality of the original class in the actual square-zero coefficients. -/
theorem coordinateClass_map {V W : FGModuleCat.{u} κ}
    (g : V ⟶ W) (a : PointedArrow x V) (b : PointedArrow x W)
    (hg : baseSpecMap ((squareZeroExtensionArtinian κ
      κ).map g) ≫ a.val = b.val) :
    tangentModuleMapAt
      (schemeDeformationBased (Λ := κ) (fibre p x))
      (isDeformationCategory_schemeDeformationCategoryProjection (fibre p x)) g
      (coordinateClass p x V a) = coordinateClass p x W b := by
  exact tangentModuleMapAt_tangentClassAt
    (schemeDeformationBased (Λ := κ) (fibre p x))
    (isDeformationCategory_schemeDeformationCategoryProjection (Λ := κ) (fibre p x)) g
    (coordinateObject p x V a) (coordinateObject p x W b)
    (coordinateChange p x g a b hg) (coordinateChange_isHomLift p x g a b hg)

/-- The original native tangent addition is computed by genuine coefficient
pushforwards of the same actual family. -/
theorem coordinateClass_add {V W : FGModuleCat.{u} κ}
    (g h : V ⟶ W) (a : PointedArrow x V)
    (b c d : PointedArrow x W)
    (hg : baseSpecMap ((squareZeroExtensionArtinian κ
      κ).map g) ≫ a.val = b.val)
    (hh : baseSpecMap ((squareZeroExtensionArtinian κ
      κ).map h) ≫ a.val = c.val)
    (hs : baseSpecMap ((squareZeroExtensionArtinian κ
      κ).map (g + h)) ≫ a.val = d.val) :
    coordinateClass p x W d = coordinateClass p x W b + coordinateClass p x W c := by
  exact tangentClassAt_add_of_isHomLift
    (schemeDeformationBased (Λ := κ) (fibre p x))
    (isDeformationCategory_schemeDeformationCategoryProjection (Λ := κ) (fibre p x)) g h
    (coordinateObject p x V a) (coordinateObject p x W b)
    (coordinateObject p x W c) (coordinateObject p x W d)
    (coordinateChange p x g a b hg) (coordinateChange_isHomLift p x g a b hg)
    (coordinateChange p x h a c hh) (coordinateChange_isHomLift p x h a c hh)
    (coordinateChange p x (g + h) a d hs) (coordinateChange_isHomLift p x (g + h) a d hs)

/-- The native unlifted residue point is the literal dual-number closed point. -/
theorem residueSpecMap_rankOne :
    residueSpecMap (coordBase (Λ := κ)
      (FGModuleCat.of κ κ)) ≫
        NativeSquareZeroCoordinates.toSpec κ (FGModuleCat.of κ κ) =
      dualNumberClosedPoint T x := by
  exact NativeSquareZeroCoordinates.residue_toSpec κ (FGModuleCat.of κ κ)

/-- The canonical tangent arrow is an actual pointed unlifted square-zero test. -/
def tangentArrow (θ : DottedTangentArrow s x) :
    PointedArrow x (FGModuleCat.of κ κ) :=
  ⟨NativeSquareZeroCoordinates.toSpec κ (FGModuleCat.of κ κ) ≫ θ.val,
    by rw [← Category.assoc, residueSpecMap_rankOne]; exact θ.property.1⟩

/-- The original first-order deformation obtained from the actual tangent arrow. -/
def tangentObject (θ : DottedTangentArrow s x) :=
  coordinateObject p x (FGModuleCat.of κ κ)
    (tangentArrow s x θ)

/-- Its total space is the literal original family pulled back along the arrow. -/
theorem tangentObject_scheme (θ : DottedTangentArrow s x) :
    (tangentObject p s x θ).val.scheme =
      pullback p (NativeSquareZeroCoordinates.toSpec κ (FGModuleCat.of κ κ) ≫ θ.val) := rfl

/-- The canonical arrow is sent to the class of that original family pullback. -/
def tangentClass (θ : DottedTangentArrow s x) :=
  coordinateClass p x (FGModuleCat.of κ κ)
    (tangentArrow s x θ)

/-- Addition of canonical tangent arrows is respected by the actual family class. -/
theorem tangentClass_add (θ η : DottedTangentArrow s x) :
    tangentClass p s x (θ + η) = tangentClass p s x θ + tangentClass p s x η := by
  obtain ⟨μ, hθ, hη, hs⟩ := (dottedTangentArrowModule s x).add_apply θ η
  let V := FGModuleCat.of κ (κ × κ)
  let W := FGModuleCat.of κ κ
  let g : V ⟶ W := FGModuleCat.ofHom (LinearMap.fst _ _ _)
  let h : V ⟶ W := FGModuleCat.ofHom (LinearMap.snd _ _ _)
  have hres : residueSpecMap (coordBase (Λ := κ) V) ≫
      NativeSquareZeroCoordinates.toSpec κ V =
        dualNumberClosedPoint T x ≫ firstDualNumberInclusion κ := by
    rw [NativeSquareZeroCoordinates.residue_toSpec]
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext z
    change z.fst = (TrivSqZeroExt.map (LinearMap.fst κ κ κ) z).fst
    rw [TrivSqZeroExt.fst_map]
  have hμ : residueSpecMap (coordBase (Λ := κ) V) ≫
      (NativeSquareZeroCoordinates.toSpec κ V ≫ μ) =
      T.fromSpecResidueField x := by
    rw [← Category.assoc, hres]
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun a => dualNumberClosedPoint T x ≫ a) hθ).trans θ.property.1)
  apply coordinateClass_add p x g h ⟨NativeSquareZeroCoordinates.toSpec κ V ≫ μ, hμ⟩
    (tangentArrow s x θ) (tangentArrow s x η) (tangentArrow s x (θ + η))
  · rw [← Category.assoc, NativeSquareZeroCoordinates.toSpec_naturality,
      Category.assoc]
    exact congrArg (fun a => NativeSquareZeroCoordinates.toSpec κ W ≫ a) hθ
  · rw [← Category.assoc, NativeSquareZeroCoordinates.toSpec_naturality,
      Category.assoc]
    exact congrArg (fun a => NativeSquareZeroCoordinates.toSpec κ W ≫ a) hη
  · rw [← Category.assoc, NativeSquareZeroCoordinates.toSpec_naturality,
      Category.assoc]
    exact congrArg (fun a => NativeSquareZeroCoordinates.toSpec κ W ≫ a) hs.symm

/-- Scaling the original dual-number parameter scales its actual family class. -/
theorem tangentClass_smul (c : κ) (θ : DottedTangentArrow s x) :
    tangentClass p s x (c • θ) = c • tangentClass p s x θ := by
  let W := FGModuleCat.of κ κ
  have hg : baseSpecMap ((squareZeroExtensionArtinian κ
      κ).map (c • 𝟙 W)) ≫ (tangentArrow s x θ).val =
        (tangentArrow s x (c • θ)).val := by
    change baseSpecMap _ ≫ (NativeSquareZeroCoordinates.toSpec κ W ≫ θ.val) =
      NativeSquareZeroCoordinates.toSpec κ W ≫ (c • θ).val
    rw [← Category.assoc, NativeSquareZeroCoordinates.toSpec_naturality,
      Category.assoc]
    exact congrArg (fun a => NativeSquareZeroCoordinates.toSpec κ W ≫ a)
      ((dottedTangentArrowModule s x).smul_apply c θ).symm
  rw [tangentClass, ← coordinateClass_map p x (c • 𝟙 W)
    (tangentArrow s x θ) (tangentArrow s x (c • θ)) hg]
  exact tangentModuleMapAt_smul _ _ c _

/-- The canonical parameter tangent map into original scheme deformations,
with linearity proved from actual square-zero coefficient changes. -/
def tangentLinearMap : DottedTangentArrow s x →ₗ[κ]
    ↥(tangentModuleAt
      (schemeDeformationBased (Λ := κ) (fibre p x))
      (isDeformationCategory_schemeDeformationCategoryProjection (fibre p x))
      (FGModuleCat.of κ κ)) where
  toFun := tangentClass p s x
  map_add' := tangentClass_add p s x
  map_smul' := tangentClass_smul p s x

end M9Native.ParameterTangentDeformation
