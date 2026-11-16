module

public import M9StacksIntegration.ParameterTangentDeformation
public import M9StacksIntegration.PointedParameterDeformation

/-!
# Original represented slice tests give canonical tangent arrows

The native square-zero spectrum is isomorphic to the ordinary dual-number
spectrum.  Inverting that actual isomorphism sends each original represented
slice test to a dotted tangent arrow, with the original residue and structural
triangles.  Its forward coordinate map is exactly the original chart map.

The slice maps and their triangle laws are from the pinned native
`StacksFrontier.Deformation.Artin.SliceTangentSpace` (Apache-2.0); no
deformation-class or Kodaira--Spencer identification is assumed here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Deformation Deformation.Examples
open Deformation.Artin Deformation.Artin.SliceTangent

universe u

namespace M9Native.SliceTangentArrowCoordinates

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.mk CategoryTheory.Functor.Fiber.fiberInclusion

/-- The genuine native coordinate isomorphism preserves the structure map. -/
theorem toSpec_comp_toBase (k : Type u) [Field k] :
    NativeSquareZeroCoordinates.toSpec k (FGModuleCat.of k k) ≫ dualNumberToBase k =
      Spec.map (CommRingCat.ofHom
        (algebraMap k (coordBase (Λ := k) (FGModuleCat.of k k)))) := by
  rw [NativeSquareZeroCoordinates.toSpec, dualNumberToBase, ← Spec.map_comp]
  congr 1

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {V : BigFppfOver B S hS}

variable (x : (B.inclusion.obj V.left))

variable {iΛ : Spec (.of (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x))) ⟶ S} {v₀ : Over V}
  {hv₀ : (Over.forget V ⋙ Over.post B.inclusion).obj v₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)) (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)))) ≫ iΛ)}
  (hpoint : pointMap hv₀ = (B.inclusion.obj V.left).fromSpecResidueField x)
  (hbase : iΛ = (B.inclusion.obj V.left).fromSpecResidueField x ≫ (B.inclusion.map V.hom))

include hpoint in
/-- The inverse coordinate map satisfies the original closed-point triangle. -/
theorem closedPoint_inverse_chartPointMap
    (z : (sliceBased iΛ v₀ hv₀).p.Fiber
      (coordBase (Λ := (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x))) (FGModuleCat.of (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)) (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x))))) :
    dualNumberClosedPoint (B.inclusion.obj V.left) x ≫
      inv (NativeSquareZeroCoordinates.toSpec (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)) (FGModuleCat.of (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)) (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)))) ≫
        chartPointMap z.val z.property = (B.inclusion.obj V.left).fromSpecResidueField x := by
  have hres : residueSpecMap (coordBase (Λ := (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)))
      (FGModuleCat.of (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)) (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)))) ≫
        NativeSquareZeroCoordinates.toSpec (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x))
          (FGModuleCat.of (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)) (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x))) =
      dualNumberClosedPoint (B.inclusion.obj V.left) x :=
    NativeSquareZeroCoordinates.residue_toSpec (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x))
      (FGModuleCat.of (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)) (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)))
  rw [← hres]
  rw [Category.assoc, IsIso.hom_inv_id_assoc]
  exact (residue_chartPointMap z.val z.property).trans hpoint

include hbase in
/-- The inverse coordinate map satisfies the original structural triangle. -/
theorem inverse_chartPointMap_comp
    (z : (sliceBased iΛ v₀ hv₀).p.Fiber
      (coordBase (Λ := (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x))) (FGModuleCat.of (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)) (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x))))) :
    (inv (NativeSquareZeroCoordinates.toSpec (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)) (FGModuleCat.of (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)) (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)))) ≫
      chartPointMap z.val z.property) ≫ (B.inclusion.map V.hom) = dualNumberBasePoint (B.inclusion.map V.hom) x := by
  rw [Category.assoc, chartPointMap_comp, ← toSpec_comp_toBase (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x))]
  simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [hbase]
  exact congrArg (dualNumberToBase (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)) ≫ ·)
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (B.inclusion.map V.hom) x).symm

/-- Every original native represented rank-one test gives a canonical dotted arrow. -/
def tangentArrow
    (z : (sliceBased iΛ v₀ hv₀).p.Fiber
      (coordBase (Λ := (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x))) (FGModuleCat.of (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)) (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x))))) : DottedTangentArrow (B.inclusion.map V.hom) x :=
  ⟨inv (NativeSquareZeroCoordinates.toSpec (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)) (FGModuleCat.of (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)) (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)))) ≫
    chartPointMap z.val z.property,
    closedPoint_inverse_chartPointMap x hpoint z,
    inverse_chartPointMap_comp x hbase z⟩

/-- The actual native coordinate image is exactly the original chart map. -/
theorem toSpec_tangentArrow
    (z : (sliceBased iΛ v₀ hv₀).p.Fiber
      (coordBase (Λ := (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x))) (FGModuleCat.of (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)) (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x))))) :
    NativeSquareZeroCoordinates.toSpec (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)) (FGModuleCat.of (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)) (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x))) ≫
      (tangentArrow x hpoint hbase z).val = chartPointMap z.val z.property := by
  exact IsIso.hom_inv_id_assoc _ _

/-- Thus the pointed native arrow of this dotted arrow is the original test map. -/
theorem pointedArrow_tangentArrow
    (z : (sliceBased iΛ v₀ hv₀).p.Fiber
      (coordBase (Λ := (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x))) (FGModuleCat.of (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x)) (IsLocalRing.ResidueField ((B.inclusion.obj V.left).presheaf.stalk x))))) :
    (ParameterTangentDeformation.tangentArrow (B.inclusion.map V.hom) x
      (tangentArrow x hpoint hbase z)).val = chartPointMap z.val z.property :=
  toSpec_tangentArrow x hpoint hbase z

end M9Native.SliceTangentArrowCoordinates
