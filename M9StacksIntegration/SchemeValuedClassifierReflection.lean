module

public import StacksFrontier.CategoryTheory.TwoYoneda.Fibered
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack

/-!
# Actual scheme maps from scheme-valued classifying morphisms

A genuine morphism to a represented native stack evaluates to an object
of the actual slice category. Its original scheme map is forced by that
slice object. A vertical transformation therefore forces equality of
the original scheme maps, rather than just equality of isomorphism classes.
No moduli space or coarse-space existence assertion is made here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.SchemeValuedClassifierReflection

universe u v uD vD

section Category

variable {C : Type u} [Category.{v} C] {U V Y : C}

/-- The actual map at a test object, including the genuine base equality. -/
def mapAt (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
    BasedCategory.ofFunctor (Over.forget Y)) (x : Over U) : x.left ⟶ Y :=
  eqToHom (F.w_obj x).symm ≫ (F.obj x).hom

/-- The slice triangle gives actual scheme-map naturality. -/
theorem mapAt_naturality (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
    BasedCategory.ofFunctor (Over.forget Y)) {x y : Over U} (a : x ⟶ y) :
    mapAt F x = a.left ≫ mapAt F y := by
  haveI : (BasedCategory.ofFunctor (Over.forget U)).p.IsHomLift a.left a :=
    CategoryTheory.IsHomLift.map (Over.forget U) a
  have hmap := BasedFunctor.preserves_isHomLift F a.left a
  haveI : (Over.forget Y).IsHomLift a.left (F.map a) := hmap
  have hleft : (F.map a).left = eqToHom (F.w_obj x) ≫ a.left ≫
      eqToHom (F.w_obj y).symm := by
    simpa using CategoryTheory.IsHomLift.fac' (Over.forget Y) a.left (F.map a)
  dsimp only [mapAt]
  rw [← Over.w (F.map a), hleft]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- A vertical transformation into the actual scheme stack forces equality. -/
theorem mapAt_eq_of_transformation
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (Over.forget Y)} (η : F ⟶ G) (x : Over U) :
    mapAt F x = mapAt G x := by
  haveI : (Over.forget Y).IsHomLift (𝟙 x.left) (η.toNatTrans.app x) :=
    η.isHomLift' x
  have hleft : (η.toNatTrans.app x).left = eqToHom (F.w_obj x) ≫
      eqToHom (G.w_obj x).symm := by
    simpa using CategoryTheory.IsHomLift.fac' (Over.forget Y)
      (𝟙 x.left) (η.toNatTrans.app x)
  dsimp only [mapAt]
  rw [← Over.w (η.toNatTrans.app x), hleft]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- The represented map is obtained by genuine native two-Yoneda evaluation. -/
def representingMap (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
    BasedCategory.ofFunctor (Over.forget Y)) : U ⟶ Y :=
  mapAt F (Functor.FiberedMor.unit U)

/-- Native slice precomposition, preserving the actual base on the nose. -/
def sliceMap (a : V ⟶ U) : BasedCategory.ofFunctor (Over.forget V) ⥤ᵇ
    BasedCategory.ofFunctor (Over.forget U) where
  toFunctor := Over.map a
  w := rfl

/-- The represented map commutes with actual base change. -/
theorem representingMap_precompose
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (Over.forget Y)) (a : V ⟶ U) :
    representingMap (BasedFunctor.comp (sliceMap a) F) = a ≫ representingMap F := by
  change mapAt F ((Over.map a).obj (Functor.FiberedMor.unit V)) =
    a ≫ mapAt F (Functor.FiberedMor.unit U)
  simpa using
      mapAt_naturality F
        (Functor.FiberedMor.toUnit ((Over.map a).obj (Functor.FiberedMor.unit V)))

/-- Genuine two-isomorphic classifying maps to a scheme have equal maps. -/
theorem representingMap_eq_of_transformation
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ
      BasedCategory.ofFunctor (Over.forget Y)} (η : F ⟶ G) :
    representingMap F = representingMap G :=
  mapAt_eq_of_transformation η _

variable {D : Type uD} [Category.{vD} D] {p : D ⥤ C}

/-- Postcomposition with a genuine native scheme-valued morphism. Different
total-category universes are retained, including those of native moduli. -/
def classifierMap
    (κ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor (Over.forget Y))
    (F : Functor.FiberedMor p U) : U ⟶ Y :=
  representingMap (BasedFunctor.comp F.toBasedFunctor κ)

/-- Actual classifier isomorphism is transported through the given genuine
scheme-valued morphism. No invariance premise is imposed on that morphism. -/
theorem classifierMap_eq_of_transformation
    (κ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor (Over.forget Y))
    {F G : Functor.FiberedMor p U} (η : F ⟶ G) :
    classifierMap κ F = classifierMap κ G :=
  representingMap_eq_of_transformation (BasedCategory.whiskerRight η κ)

end Category

section NativeScheme

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {D : Type uD} [Category.{vD} D] {p : D ⥤ BigFppfOver B S hS}
  {U Y : BigFppfOver B S hS}

/-- The original scheme map underlying the genuine represented-stack value. -/
def originalClassifierMap
    (κ : BasedCategory.ofFunctor p ⥤ᵇ (Stack.schemeFibredCategory B S hS Y).val)
    (F : Functor.FiberedMor p U) :
    (BigFppfOver.toScheme B S hS).obj U ⟶ (BigFppfOver.toScheme B S hS).obj Y :=
  (BigFppfOver.toScheme B S hS).map (classifierMap κ F)

/-- Equality is reflected to the SAME original schemes, with actual base maps. -/
theorem originalClassifierMap_eq
    (κ : BasedCategory.ofFunctor p ⥤ᵇ (Stack.schemeFibredCategory B S hS Y).val)
    {F G : Functor.FiberedMor p U} (η : F ⟶ G) :
    originalClassifierMap B S hS κ F = originalClassifierMap B S hS κ G :=
  congrArg (BigFppfOver.toScheme B S hS).map
    (classifierMap_eq_of_transformation κ η)

/-- After equality on the actual common-domain scheme, every ORIGINAL test
scheme may pull it back. No bounded-site membership of this test is needed. -/
theorem originalClassifierMap_eq_on_all_tests
    (κ : BasedCategory.ofFunctor p ⥤ᵇ (Stack.schemeFibredCategory B S hS Y).val)
    {F G : Functor.FiberedMor p U} (η : F ⟶ G)
    (T : Scheme.{u}) (a : T ⟶ (BigFppfOver.toScheme B S hS).obj U) :
    a ≫ originalClassifierMap B S hS κ F = a ≫ originalClassifierMap B S hS κ G :=
  congrArg (fun f => a ≫ f) (originalClassifierMap_eq B S hS κ η)

end NativeScheme

end M9Native.SchemeValuedClassifierReflection
