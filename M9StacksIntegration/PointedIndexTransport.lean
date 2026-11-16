module

public import StacksFrontier.Deformation.Artin.Predeformation.Transport

/-!
# Actual index transport of a pointed deformation category

Equal structural maps give an identity equivalence on the original
Artinian fibre and the original marked family. The coordinate formulas
are proved by equality elimination, not assumed for a concrete model.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Deformation Deformation.Artin
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe u v w
namespace M9Native.PointedIndexTransport

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  {S : Scheme.{u}} {C : Type v} [Category.{w} C]
  (q : C ⥤ Over S) (x : C) (a b : Spec (.of Λ) ⟶ S)
  (ha : q.obj x = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ a))
  (hb : q.obj x = Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ b))
  (h : a = b)

/-- The literal identity transport along equality of the actual structural maps. -/
def equivalence :
    letI := (predeformationCategory a q x ha).category
    letI := (predeformationCategory b q x hb).category
    StacksRepresentableCFG.EquivalenceOver
      (predeformationCategory a q x ha).projection
      (predeformationCategory b q x hb).projection := by
  subst b
  exact StacksRepresentableCFG.EquivalenceOver.refl
    (predeformationCategory a q x ha).projection

/-- The original Artinian algebra is unchanged. -/
theorem object_algebra (d : (predeformationCategory a q x ha).carrier) :
    ((predeformationCategory b q x hb).objects
      ((equivalence q x a b ha hb h).hom.functor.obj d)).algebra =
      ((predeformationCategory a q x ha).objects d).algebra := by
  subst b
  rfl

/-- The actual family object is unchanged. -/
theorem object_point (d : (predeformationCategory a q x ha).carrier) :
    ((predeformationCategory b q x hb).objects
      ((equivalence q x a b ha hb h).hom.functor.obj d)).point =
      ((predeformationCategory a q x ha).objects d).point := by
  subst b
  rfl

/-- The actual marking is unchanged, with its proved literal endpoint cast. -/
theorem object_arrow (d : (predeformationCategory a q x ha).carrier) :
    ((predeformationCategory b q x hb).objects
      ((equivalence q x a b ha hb h).hom.functor.obj d)).arrow =
      ((predeformationCategory a q x ha).objects d).arrow ≫
        eqToHom (object_point q x a b ha hb h d).symm := by
  subst b
  exact (Category.comp_id _).symm

end M9Native.PointedIndexTransport
