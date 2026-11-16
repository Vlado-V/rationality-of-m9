module

public import StacksFrontier.Deformation.Artin.Predeformation.Transport

/-!
# Genuine pointed transport along a vertical base-point isomorphism

The equivalence is constructed from the actual isomorphism; its functor
leaves the deformation point and Artinian algebra fixed and precomposes
the marked arrow. This is the native pointed change used by a family
classifier's canonical point-value comparison.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Deformation Deformation.Artin
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe u v w
namespace M9Native.PointedBasePointTransport

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  (iΛ : Spec (.of Λ) ⟶ S) {C : Type v} [Category.{w} C]
  (p : C ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (x y : C)
  (hx : (p ⋙ Over.post B.inclusion).obj x =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (hy : (p ⋙ Over.post B.inclusion).obj y =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
  (e : x ≅ y)
  (he : (p ⋙ Over.post B.inclusion).map e.hom = eqToHom (hx.trans hy.symm))

include he in
/-- The inverse original base-point isomorphism is vertical in the exact native coordinates. -/
theorem inverse_base :
    (p ⋙ Over.post B.inclusion).map e.inv = eqToHom (hy.trans hx.symm) := by
  apply (cancel_mono ((p ⋙ Over.post B.inclusion).map e.hom)).mp
  rw [← CategoryTheory.Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id, he]
  simp only [eqToHom_trans, eqToHom_refl]

/-- The actual based-point equivalence on the original deformation categories. -/
def equivalence :
    letI := (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x hx).category
    letI := (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) y hy).category
    StacksRepresentableCFG.EquivalenceOver
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) y hy).projection
      (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x hx).projection := by
  letI := (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x hx).category
  letI := (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) y hy).category
  have he' : (p ⋙ Over.post B.inclusion).map e.hom =
      eqToHom (hx.trans
        ((transport_obj_eq B hS p p (𝟭 C) (Functor.id_comp p) y).trans hy).symm) := he
  refine transportPredeformationEquivalence B hS iΛ p p (𝟭 C)
    (Functor.id_comp p) y hy x hx e.hom hp hp he'
    (fun a b β _ => ⟨β, rfl⟩) ?_
  intro c
  have hi : (p ⋙ Over.post B.inclusion).map e.inv =
      eqToHom (hy.trans
        ((transport_obj_eq B hS p p (𝟭 C) (Functor.id_comp p) x).trans hx).symm) :=
    inverse_base B hS iΛ p x y hx hy e he
  let d := transportDeformationObject B hS iΛ p p (𝟭 C)
    (Functor.id_comp p) x hx y hy e.inv hi c
  refine ⟨d, 𝟙 c.point, rfl, rfl, ?_, ?_⟩
  · change c.arrow ≫ 𝟙 _ = e.hom ≫ (e.inv ≫ c.arrow)
    simp
  · change (p ⋙ Over.post B.inclusion).map (𝟙 c.point) = eqToHom (rfl : _ = _)
    simp only [CategoryTheory.Functor.map_id, eqToHom_refl]

/-- The original transport functor fixes the actual deformation point. -/
theorem object_point
    (d : (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) y hy).carrier) :
    ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x hx).objects
      ((equivalence B hS iΛ p hp x y hx hy e he).hom.functor.obj d)).point =
      ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) y hy).objects d).point := rfl

/-- It changes only the original marking, by the actual base-point isomorphism. -/
theorem object_arrow
    (d : (predeformationCategory iΛ (p ⋙ Over.post B.inclusion) y hy).carrier) :
    ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) x hx).objects
      ((equivalence B hS iΛ p hp x y hx hy e he).hom.functor.obj d)).arrow =
      e.hom ≫ ((predeformationCategory iΛ (p ⋙ Over.post B.inclusion) y hy).objects d).arrow := rfl

end M9Native.PointedBasePointTransport
