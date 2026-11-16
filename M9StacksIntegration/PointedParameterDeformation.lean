module

public import M9StacksIntegration.ParameterFamilyDeformation
public import StacksFrontier.Deformation.Artin.SliceTangentSpace

/-!
# The actual family functor from represented pointed deformations

Objects are the original native predeformations of a point of a represented
scheme. Their images are the literal pullbacks of the specified flat family,
with its original special-fibre map. No tangent comparison or lifting
property is supplied to this construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Deformation
open Deformation.Artin Deformation.Artin.SliceTangent Deformation.Examples

universe u

namespace M9Native.PointedParameterDeformation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {V : BigFppfOver B S hS}
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  {iΛ : Spec (.of Λ) ⟶ S} {v₀ : Over V}
  {hv₀ : (Over.forget V ⋙ Over.post B.inclusion).obj v₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}

variable {X : Scheme.{u}} (p : X ⟶ B.inclusion.obj V.left) [Flat p]

/-- The original scheme fibre at the actual represented field point. -/
abbrev fibre := ParameterFamilyDeformation.fibre p (pointMap hv₀)

/-- The native residue map is exactly the one used by scheme deformations. -/
theorem residueSpecMap_eq (A : ArtinianLocalAlgCat.{u, u, u} Λ k) :
    residueSpecMap A = Spec.map (CommRingCat.ofHom (residueMap A)) := rfl

/-- Read a native represented predeformation as the original pulled family. -/
def familyObject (a : (sliceDeformations iΛ v₀ hv₀).carrier) :
    SchemeDeformationCategory (Λ := Λ) (fibre (hv₀ := hv₀) p) :=
  ParameterFamilyDeformation.deformation p (pointMap hv₀) a.algebra
    (deformationMap a) (residue_deformationMap a)

/-- The image retains the original Artinian algebra, without a base change. -/
theorem familyObject_base (a : (sliceDeformations iΛ v₀ hv₀).carrier) :
    (familyObject p a).base = a.algebra := rfl

/-- The total space is the literal pullback by the native deformation map. -/
theorem familyObject_scheme (a : (sliceDeformations iΛ v₀ hv₀).carrier) :
    (familyObject p a).scheme = pullback p (deformationMap a) := rfl

/-- Every reversed native parameter arrow induces the actual pullback arrow
of the family, with exactly the same Artinian ring map. -/
def familyMap {a b : (sliceDeformations iΛ v₀ hv₀).carrier} (m : a ⟶ b) :
    familyObject p a ⟶ familyObject p b :=
  ParameterFamilyDeformation.changeTest p (pointMap hv₀)
    (deformationMap a) (residue_deformationMap a)
    (deformationMap b) (residue_deformationMap b)
    m.ringHom (deformationMap_of_morphism m).symm

/-- Its base map is the original ring map of the native deformation arrow. -/
theorem familyMap_base {a b : (sliceDeformations iΛ v₀ hv₀).carrier} (m : a ⟶ b) :
    (familyMap p m).base = m.ringHom := rfl

/-- The original flat family defines a genuine functor from the native
represented-point predeformation category to scheme deformations. -/
def familyFunctor : (sliceDeformations iΛ v₀ hv₀).carrier ⥤
    SchemeDeformationCategory (Λ := Λ) (fibre (hv₀ := hv₀) p) where
  obj := familyObject p
  map := familyMap p
  map_id a := by
    apply SchemeDeformationCategory.Hom.ext
    · rfl
    · change (familyMap p (𝟙 a)).map = 𝟙 _
      apply pullback.hom_ext
      · simp [familyMap, ParameterFamilyDeformation.changeTest]
      · simp only [familyMap, ParameterFamilyDeformation.changeTest, pullback.lift_snd]
        change _ ≫ baseSpecMap (𝟙 a.algebra) = _
        simp only [baseSpecMap_id, Category.comp_id, Category.id_comp]
  map_comp m n := by
    apply SchemeDeformationCategory.Hom.ext
    · rfl
    · change (familyMap p (m ≫ n)).map = (familyMap p n).map ≫ (familyMap p m).map
      apply pullback.hom_ext
      · simp [familyMap, ParameterFamilyDeformation.changeTest]
      · simp only [familyMap, ParameterFamilyDeformation.changeTest, Category.assoc,
          pullback.lift_snd, pullback.lift_snd_assoc]
        change _ ≫ baseSpecMap (m.ringHom ≫ n.ringHom) = _
        rw [baseSpecMap_comp]

/-- The functor commutes with the actual Artinian projections literally. -/
theorem familyFunctor_projection : familyFunctor (hv₀ := hv₀) p ⋙
    schemeDeformationCategoryProjection (Λ := Λ) (fibre (hv₀ := hv₀) p) =
      (sliceDeformations iΛ v₀ hv₀).projection := rfl

/-- The actual family as a based functor, retaining the original projection. -/
def familyBased : sliceBased iΛ v₀ hv₀ ⥤ᵇ
    schemeDeformationBased (Λ := Λ) (fibre (hv₀ := hv₀) p) where
  toFunctor := familyFunctor p
  w := familyFunctor_projection p

/-- On an actual fibre object the image is precisely the specified pulled
family, with the original equality identifying its base. -/
theorem fiberFunctor_obj (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (a : (sliceBased iΛ v₀ hv₀).p.Fiber A) :
    (fiberFunctor (familyBased p) A).obj a =
      ⟨ParameterFamilyDeformation.deformation p (pointMap hv₀) a.val.algebra
        (deformationMap a.val) (residue_deformationMap a.val), a.property⟩ := rfl

variable
  (hfinite : LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hqc : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))

include hfinite hqc in
/-- The canonical native deformation structure on the represented point. -/
theorem representedDeformation : IsDeformationCategory (sliceBased iΛ v₀ hv₀).p :=
  isDeformationCategory_sliceDeformations hfinite hqc

/-- The induced differential of the actual family functor, for every finite
coefficient module, not an assigned Kodaira--Spencer map. -/
def familyTangent (W : FGModuleCat.{u} k) :
    ↥(tangentModuleAt.{u, u, u} (sliceBased iΛ v₀ hv₀)
      (representedDeformation (hv₀ := hv₀) hfinite hqc) W) →ₗ[k]
    ↥(tangentModuleAt.{u, u, u} (schemeDeformationBased (Λ := Λ) (fibre (hv₀ := hv₀) p))
      (isDeformationCategory_schemeDeformationCategoryProjection (fibre (hv₀ := hv₀) p)) W) :=
  tangentMapAt.{u, u, u} (representedDeformation hfinite hqc)
    (isDeformationCategory_schemeDeformationCategoryProjection (fibre (hv₀ := hv₀) p))
    (familyBased p) W

/-- The differential's value is the original native class of the literal
pulled family on the same square-zero algebra and coefficient module. -/
theorem familyTangent_class (W : FGModuleCat.{u} k)
    (a : (sliceBased iΛ v₀ hv₀).p.Fiber
      ((squareZeroExtensionArtinian Λ k).obj W)) :
    familyTangent p hfinite hqc W
      (tangentClassAt.{u, u, u} (sliceBased iΛ v₀ hv₀) (representedDeformation hfinite hqc) W a) =
    tangentClassAt.{u, u, u} (schemeDeformationBased (Λ := Λ) (fibre (hv₀ := hv₀) p))
      (isDeformationCategory_schemeDeformationCategoryProjection (fibre (hv₀ := hv₀) p)) W
      ⟨ParameterFamilyDeformation.deformation p (pointMap hv₀) a.val.algebra
        (deformationMap a.val) (residue_deformationMap a.val), a.property⟩ :=
  tangentMapAt_tangentClassAt.{u, u, u} (representedDeformation hfinite hqc)
    (isDeformationCategory_schemeDeformationCategoryProjection (fibre (hv₀ := hv₀) p))
    (familyBased p) W a

/-- Two parameter tangent classes have the same family derivative precisely
when the actual pulled families are isomorphic over the identity of their
common square-zero base. This retains the genuine relative kernel. -/
theorem familyTangent_class_eq_iff (W : FGModuleCat.{u} k)
    (a b : (sliceBased iΛ v₀ hv₀).p.Fiber
      ((squareZeroExtensionArtinian Λ k).obj W)) :
    familyTangent p hfinite hqc W
        (tangentClassAt.{u, u, u} (sliceBased iΛ v₀ hv₀) (representedDeformation hfinite hqc) W a) =
      familyTangent p hfinite hqc W
        (tangentClassAt.{u, u, u} (sliceBased iΛ v₀ hv₀) (representedDeformation hfinite hqc) W b) ↔
      IsIsomorphic
        ((fiberFunctor (familyBased p) ((squareZeroExtensionArtinian Λ k).obj W)).obj a)
        ((fiberFunctor (familyBased p) ((squareZeroExtensionArtinian Λ k).obj W)).obj b) := by
  rw [familyTangent_class, familyTangent_class]
  exact tangentClassAt_eq_iff.{u, u, u} _ _ W _ _

end M9Native.PointedParameterDeformation
