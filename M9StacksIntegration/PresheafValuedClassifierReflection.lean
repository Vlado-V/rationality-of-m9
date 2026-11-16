module

public import StacksFrontier.CategoryTheory.TwoYoneda.Fibered
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSectionIso

/-! Genuine presheaf maps from classifying functors with a discrete target.
The construction is actual Yoneda evaluation; vertical transformations force
literal equality of the resulting morphisms of presheaves. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open CategoryTheory Opposite
open CategoryTheory.PresheafOfCategories
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.PresheafValuedClassifierReflection

universe v u vD uD
variable {C : Type u} [Category.{v} C] (P : Cᵒᵖ ⥤ Type v)

/-- The actual category of elements of the presheaf, over its original base. -/
abbrev elementsBased := BasedCategory.ofFunctor (discreteProjection P)

variable {P} {U V : C}

/-- The genuine element named by a based functor at an actual test object. -/
def mapAt (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ elementsBased P)
    (x : Over U) : P.obj (op x.left) :=
  sectionOfBasedFunctor F.toFunctor F.w x

/-- The element is compatible with the actual arrow between test objects. -/
theorem mapAt_naturality
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ elementsBased P)
    {x y : Over U} (a : x ⟶ y) :
    P.map a.left.op (mapAt F y) = mapAt F x :=
  sectionOfBasedFunctor_map F.toFunctor F.w a

/-- A vertical transformation gives equality in the discrete presheaf. -/
theorem mapAt_eq_of_transformation
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ elementsBased P}
    (η : F ⟶ G) (x : Over U) : mapAt F x = mapAt G x := by
  have he : F.toFunctor = G.toFunctor :=
    eq_of_vertical_natTrans F.w G.w η.toNatTrans (fun x => η.isHomLift' x)
  exact sectionOfBasedFunctor_congr F.toFunctor G.toFunctor F.w G.w
    (congrArg (fun H => H.obj x) he)

/-- The actual presheaf morphism given by Yoneda evaluation. -/
def representingMap
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ elementsBased P) :
    yoneda.obj U ⟶ P :=
  yonedaEquiv.symm (mapAt F (Functor.FiberedMor.unit U))

/-- On EVERY actual test arrow, the morphism has its named value. -/
theorem representingMap_app
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ elementsBased P)
    (T : C) (a : T ⟶ U) :
    (representingMap F).app (op T) a = mapAt F (Over.mk a) := by
  change P.map a.op (mapAt F (Functor.FiberedMor.unit U)) = _
  exact mapAt_naturality F (Functor.FiberedMor.toUnit (Over.mk a))

/-- Genuine precomposition on the native slice, retaining its base. -/
def sliceMap (a : V ⟶ U) : BasedCategory.ofFunctor (Over.forget V) ⥤ᵇ
    BasedCategory.ofFunctor (Over.forget U) where
  toFunctor := Over.map a
  w := rfl

/-- Yoneda maps commute with actual precomposition of classifiers. -/
theorem representingMap_precompose
    (F : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ elementsBased P) (a : V ⟶ U) :
    representingMap (BasedFunctor.comp (sliceMap a) F) = yoneda.map a ≫ representingMap F := by
  apply yonedaEquiv.injective
  rw [← yonedaEquiv_naturality]
  simp only [representingMap, Equiv.apply_symm_apply]
  change mapAt F ((Over.map a).obj (Functor.FiberedMor.unit V)) =
    P.map a.op (mapAt F (Functor.FiberedMor.unit U))
  simpa [Functor.FiberedMor.unit] using (mapAt_naturality F
    (Functor.FiberedMor.toUnit ((Over.map a).obj (Functor.FiberedMor.unit V)))).symm

/-- Genuine two-isomorphic classifiers induce identical presheaf maps. -/
theorem representingMap_eq_of_transformation
    {F G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ elementsBased P}
    (η : F ⟶ G) : representingMap F = representingMap G :=
  congrArg (fun t => yonedaEquiv.symm t)
    (mapAt_eq_of_transformation η (Functor.FiberedMor.unit U))

variable {D : Type uD} [Category.{vD} D] {p : D ⥤ C}

/-- Postcompose an actual classifier with a genuine presheaf-valued morphism. -/
def classifierMap (κ : BasedCategory.ofFunctor p ⥤ᵇ elementsBased P)
    (F : Functor.FiberedMor p U) : yoneda.obj U ⟶ P :=
  representingMap (BasedFunctor.comp F.toBasedFunctor κ)

/-- Invariance is DERIVED from the actual classifier transformation. -/
theorem classifierMap_eq_of_transformation
    (κ : BasedCategory.ofFunctor p ⥤ᵇ elementsBased P)
    {F G : Functor.FiberedMor p U} (η : F ⟶ G) :
    classifierMap κ F = classifierMap κ G :=
  representingMap_eq_of_transformation (BasedCategory.whiskerRight η κ)

end M9Native.PresheafValuedClassifierReflection
