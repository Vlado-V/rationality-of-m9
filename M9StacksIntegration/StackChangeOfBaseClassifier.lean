module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseStack
public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift
public import StacksFrontier.CategoryTheory.TwoYoneda.Fibered

/-! The original classifier lifts to the actual native change of base.
The strict-pullback projection retains its original objects and arrows.
Vertical arrows in the actual base-changed stack project to vertical arrows
in the original stack; no comparison of source models is an input. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.StackChangeOfBaseClassifier

universe u w
variable (B : BigFppfSite.{u}) (S S' : Scheme.{u})
  (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS') (𝒳 : Stack.AlgebraicStacks.{u, w} B S' hS')

/-- The literal native stack change of base, with its given coefficient map. -/
abbrev changedStack := Stack.changeOfBase B S S' hS hS' g 𝒳

/-- The original-stack projection of the actual strict pullback. -/
abbrev originalProjection :
    (changedStack B S S' hS hS' g 𝒳).val.val.obj ⥤ 𝒳.val.val.obj :=
  StrictPullback.pr (Over.map g) 𝒳.val.val.p

/-- Its square commutes with the actual original structure functor. -/
theorem originalProjection_comp :
    originalProjection B S S' hS hS' g 𝒳 ⋙ 𝒳.val.val.p =
      (changedStack B S S' hS hS' g 𝒳).val.val.p ⋙ Over.map g :=
  StrictPullback.pr_comp_eq _ _

/-- The original basedness gives the strict-pullback triangle. -/
theorem lift_triangle (T : BigFppfOver B S hS)
    (F : Functor.FiberedMor 𝒳.val.val.p ((Over.map g).obj T)) :
    (Over.post (Over.map g) ⋙ F.toFunctor) ⋙ 𝒳.val.val.p =
      Over.forget T ⋙ Over.map g := by
  have hw : F.toFunctor ⋙ 𝒳.val.val.p =
      Over.forget ((Over.map g).obj T) := F.w
  rw [Functor.assoc, hw]
  rfl

/-- Lift the specified original classifier, along the actual structural
map of its base, into the genuine native change of base. -/
def lift (T : BigFppfOver B S hS)
    (F : Functor.FiberedMor 𝒳.val.val.p ((Over.map g).obj T)) :
    BasedCategory.ofFunctor (Over.forget T) ⥤ᵇ
      (changedStack B S S' hS hS' g 𝒳).val.val where
  toFunctor := StrictPullback.liftFib (Over.forget T)
    (Over.post (Over.map g) ⋙ F.toFunctor)
    (lift_triangle B S S' hS hS' g 𝒳 T F)
  w := rfl

/-- The projected functor is the SAME original classifier at every slice object. -/
theorem lift_original (T : BigFppfOver B S hS)
    (F : Functor.FiberedMor 𝒳.val.val.p ((Over.map g).obj T)) :
    (lift B S S' hS hS' g 𝒳 T F).toFunctor ⋙
        originalProjection B S S' hS hS' g 𝒳 =
      Over.post (Over.map g) ⋙ F.toFunctor := rfl

/-- Every lifted object retains the specified field-base object literally. -/
theorem lift_obj_base (T : BigFppfOver B S hS)
    (F : Functor.FiberedMor 𝒳.val.val.p ((Over.map g).obj T)) (x : Over T) :
    (changedStack B S S' hS hS' g 𝒳).val.val.p.obj
      ((lift B S S' hS hS' g 𝒳 T F).obj x) = x.left := rfl

/-- Every lifted original-family object is retained literally. -/
theorem lift_obj_original (T : BigFppfOver B S hS)
    (F : Functor.FiberedMor 𝒳.val.val.p ((Over.map g).obj T)) (x : Over T) :
    (originalProjection B S S' hS hS' g 𝒳).obj
        ((lift B S S' hS hS' g 𝒳 T F).obj x) =
      F.toFunctor.obj ((Over.post (Over.map g)).obj x) := rfl

/-- Every original-family arrow, including its total-space map, is retained. -/
theorem lift_map_original (T : BigFppfOver B S hS)
    (F : Functor.FiberedMor 𝒳.val.val.p ((Over.map g).obj T))
    {x y : Over T} (a : x ⟶ y) :
    (originalProjection B S S' hS hS' g 𝒳).map
        ((lift B S S' hS hS' g 𝒳 T F).map a) =
      F.toFunctor.map ((Over.post (Over.map g)).map a) := rfl

/-- A genuine identity-base arrow in the actual changed stack projects to
an identity-base arrow in the original stack. This also applies to
classifiers precomposed with arbitrary slice maps. -/
theorem projected_isHomLift_id
    {x y : (changedStack B S S' hS hS' g 𝒳).val.val.obj}
    (T : BigFppfOver B S hS) (a : x ⟶ y)
    (ha : (changedStack B S S' hS hS' g 𝒳).val.val.p.IsHomLift (𝟙 T) a) :
    𝒳.val.val.p.IsHomLift (𝟙 ((Over.map g).obj T))
      ((originalProjection B S S' hS hS' g 𝒳).map a) := by
  have h := Functor.isHomLift_id_comp_functor (Over.map g) ha
  rw [← originalProjection_comp B S S' hS hS' g 𝒳] at h
  exact (Functor.isHomLift_comp_iff
    (originalProjection B S S' hS hS' g 𝒳) 𝒳.val.val.p _ a).mp h

/-- The lifted classifier itself is a genuine morphism of native stacks. -/
def stackMorphism (T : BigFppfOver B S hS)
    (F : Functor.FiberedMor 𝒳.val.val.p ((Over.map g).obj T)) :
    Stack.schemeStack.{u, w} B S hS T ⟶ changedStack B S S' hS hS' g 𝒳 :=
  Bicategory.InducedBicategory.mkHom
    (Bicategory.InducedBicategory.mkHom (lift B S S' hS hS' g 𝒳 T F))

/-- Its native functor is exactly the constructed original classifier lift. -/
theorem stackMorphism_functor (T : BigFppfOver B S hS)
    (F : Functor.FiberedMor 𝒳.val.val.p ((Over.map g).obj T)) :
    (stackMorphism B S S' hS hS' g 𝒳 T F).hom.hom.toFunctor =
      (lift B S S' hS hS' g 𝒳 T F).toFunctor := rfl

end M9Native.StackChangeOfBaseClassifier
