module

public import M9StacksIntegration.GenusNineCoarseOverField
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.ModuliSpaceBasics
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSectionIso

/-! Categorical factorization through the independently chosen native coarse space.

A based functor from the actual field-base smooth curve stack to an actual
native algebraic space is already a morphism of categories fibred in
groupoids. The actual uniform coarse-map theorem therefore gives its unique
factorization. The resulting invertible 2-morphism is also read as literal
section equations on every object of the same chosen source.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.PresheafOfCategories
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.GenusNineCoarseCategoricalFactorization

open M9StacksIntegration

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (g : ℕ) (hg : 2 ≤ g)
  (W : AlgebraicSpaces B (Spec (.of K)) hK)
  (H : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val ⥤ᵇ
    (Stack.fibredCategory B (Spec (.of K)) hK W.obj).val)

/-- The given based functor is a genuine morphism of categories fibred in groupoids. -/
def classifierMorphism :
    (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val ⟶
      Stack.fibredCategory B (Spec (.of K)) hK W.obj :=
  Bicategory.InducedBicategory.mkHom H

/-- Its underlying functor is the original based functor, literally. -/
theorem classifierMorphism_functor :
    (classifierMorphism B hZ K hK g hg W H).hom.toFunctor = H.toFunctor := rfl

/-- Cartesian preservation follows from the actual groupoid-fibred source and target. -/
theorem classifierMorphism_cartesian
    {R S : BigFppfOver B (Spec (.of K)) hK}
    {x y : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj}
    (a : R ⟶ S) (α : x ⟶ y)
    [(GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.p.IsHomLift a α] :
    (Stack.fibredCategory B (Spec (.of K)) hK W.obj).val.p.IsStronglyCartesian a
      (H.toFunctor.map α) :=
  CatFiberedInGroupoids.isStronglyCartesian_map
    (classifierMorphism B hZ K hK g hg W H) a α

/-- Categorical universality is derived from the actual uniform coarse-map theorem. -/
theorem coarseMap_categorical :
    Stack.IsCategoricalModuliSpace B (Spec (.of K)) hK
      (GenusNineCoarseOverField.coarseSpace B hZ K hK g hg)
      (GenusNineCoarseOverField.coarseMap B hZ K hK g hg).hom :=
  Stack.isCategoricalModuliSpace_of_isUniformCategoricalModuliSpace B (Spec (.of K)) hK
    (GenusNineCoarseOverField.coarseMap_uniform B hZ K hK g hg)

/-- The element of the native target named by the given functor on an actual source object. -/
def namedValue
    (x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj) :
    W.obj.obj (op ((GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.p.obj x)) :=
  sectionOfBasedFunctor H.toFunctor H.w x

/-- The element of the independently chosen coarse space named by its actual coarse map. -/
def coarseValue
    (x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj) :
    (GenusNineCoarseOverField.coarseSpace B hZ K hK g hg).obj.obj
      (op ((GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.p.obj x)) :=
  sectionOfBasedFunctor (GenusNineCoarseOverField.coarseMap B hZ K hK g hg).hom.hom.toFunctor
    (GenusNineCoarseOverField.coarseMap B hZ K hK g hg).hom.hom.w x

/-- There is a unique actual native map with the genuine categorical factorization. -/
theorem existsUnique_factorization :
    ∃! f : GenusNineCoarseOverField.coarseSpace B hZ K hK g hg ⟶ W,
      Nonempty ((GenusNineCoarseOverField.coarseMap B hZ K hK g hg).hom ≫
        (Stack.associatedMap B (Spec (.of K)) hK f.hom).1 ≅
          classifierMorphism B hZ K hK g hg W H) :=
  coarseMap_categorical B hZ K hK g hg W (classifierMorphism B hZ K hK g hg W H)

/-- The unique native map supplied by actual coarse universality. -/
def factorMap : GenusNineCoarseOverField.coarseSpace B hZ K hK g hg ⟶ W :=
  (existsUnique_factorization B hZ K hK g hg W H).choose

/-- Its actual factorization 2-isomorphism. -/
def factorIso :
    (GenusNineCoarseOverField.coarseMap B hZ K hK g hg).hom ≫
      (Stack.associatedMap B (Spec (.of K)) hK (factorMap B hZ K hK g hg W H).hom).1 ≅
        classifierMorphism B hZ K hK g hg W H :=
  (existsUnique_factorization B hZ K hK g hg W H).choose_spec.1.some

/-- Every genuine factorization uses the same native map. -/
theorem factorMap_unique
    (f : GenusNineCoarseOverField.coarseSpace B hZ K hK g hg ⟶ W)
    (hf : Nonempty ((GenusNineCoarseOverField.coarseMap B hZ K hK g hg).hom ≫
      (Stack.associatedMap B (Spec (.of K)) hK f.hom).1 ≅
        classifierMorphism B hZ K hK g hg W H)) :
    f = factorMap B hZ K hK g hg W H :=
  (existsUnique_factorization B hZ K hK g hg W H).choose_spec.2 f hf

/-- Postcomposing the actual coarse map applies the native map to its named value. -/
theorem postcompose_namedValue
    (f : GenusNineCoarseOverField.coarseSpace B hZ K hK g hg ⟶ W)
    (x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj) :
    sectionOfBasedFunctor
        ((GenusNineCoarseOverField.coarseMap B hZ K hK g hg).hom ≫
          (Stack.associatedMap B (Spec (.of K)) hK f.hom).1).hom.toFunctor
        ((GenusNineCoarseOverField.coarseMap B hZ K hK g hg).hom ≫
          (Stack.associatedMap B (Spec (.of K)) hK f.hom).1).hom.w x =
      f.hom.app (op ((GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.p.obj x))
        (coarseValue B hZ K hK g hg x) := by
  have hobj :
      ((GenusNineCoarseOverField.coarseMap B hZ K hK g hg).hom ≫
        (Stack.associatedMap B (Spec (.of K)) hK f.hom).1).hom.obj x =
      ⟨(GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.p.obj x,
        Discrete.mk (f.hom.app
          (op ((GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.p.obj x))
          (coarseValue B hZ K hK g hg x))⟩ := by
    change (Stack.associatedMap B (Spec (.of K)) hK f.hom).1.hom.obj
      ((GenusNineCoarseOverField.coarseMap B hZ K hK g hg).hom.hom.obj x) = _
    rw [Stack.obj_eq_mk_section B (Spec (.of K)) hK
      (GenusNineCoarseOverField.coarseMap B hZ K hK g hg).hom x,
      Stack.associatedMap_obj]
    rfl
  exact elementOf_congr _ rfl hobj

/-- A genuine factorization 2-isomorphism gives literal section equations on all objects. -/
theorem factorization_sections_of_iso
    (f : GenusNineCoarseOverField.coarseSpace B hZ K hK g hg ⟶ W)
    (η : (GenusNineCoarseOverField.coarseMap B hZ K hK g hg).hom ≫
      (Stack.associatedMap B (Spec (.of K)) hK f.hom).1 ≅
        classifierMorphism B hZ K hK g hg W H)
    (x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj) :
    f.hom.app (op ((GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.p.obj x))
        (coarseValue B hZ K hK g hg x) = namedValue B hZ K hK g hg W H x := by
  rw [← postcompose_namedValue B hZ K hK g hg W f x]
  exact Stack.section_eq_of_obj_eq B (Spec (.of K)) hK _ _ x
    (congrArg (fun F => F.hom.obj x) (Stack.hom_eq_of_hom₂ B (Spec (.of K)) hK η.hom))

/-- Genuine 2-isomorphism factorization is equivalent to all the actual section equations. -/
theorem factorization_iff_sections
    (f : GenusNineCoarseOverField.coarseSpace B hZ K hK g hg ⟶ W) :
    Nonempty ((GenusNineCoarseOverField.coarseMap B hZ K hK g hg).hom ≫
      (Stack.associatedMap B (Spec (.of K)) hK f.hom).1 ≅
        classifierMorphism B hZ K hK g hg W H) ↔
    ∀ x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj,
      f.hom.app (op ((GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.p.obj x))
        (coarseValue B hZ K hK g hg x) = namedValue B hZ K hK g hg W H x := by
  constructor
  · rintro ⟨η⟩ x
    exact factorization_sections_of_iso B hZ K hK g hg W H f η x
  · intro h
    refine ⟨eqToIso (Stack.hom_ext_of_section B (Spec (.of K)) hK _ _ ?_)⟩
    intro x
    rw [postcompose_namedValue B hZ K hK g hg W f x]
    exact h x

/-- The chosen unique native map satisfies every actual named-value equation. -/
theorem factorization_sections
    (x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj) :
    (factorMap B hZ K hK g hg W H).hom.app
        (op ((GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.p.obj x))
        (coarseValue B hZ K hK g hg x) = namedValue B hZ K hK g hg W H x :=
  factorization_sections_of_iso B hZ K hK g hg W H
    (factorMap B hZ K hK g hg W H) (factorIso B hZ K hK g hg W H) x

/-- There is a unique native map satisfying the literal equations on all actual source objects. -/
theorem existsUnique_section_factorization :
    ∃! f : GenusNineCoarseOverField.coarseSpace B hZ K hK g hg ⟶ W,
      ∀ x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj,
        f.hom.app (op ((GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.p.obj x))
          (coarseValue B hZ K hK g hg x) = namedValue B hZ K hK g hg W H x := by
  refine ⟨factorMap B hZ K hK g hg W H, factorization_sections B hZ K hK g hg W H, ?_⟩
  intro f hf
  exact factorMap_unique B hZ K hK g hg W H f
    ((factorization_iff_sections B hZ K hK g hg W H f).mpr hf)

/-- Equality with the unique factor is detected by the same literal source-value equations. -/
theorem factorMap_eq_iff_sections
    (f : GenusNineCoarseOverField.coarseSpace B hZ K hK g hg ⟶ W) :
    f = factorMap B hZ K hK g hg W H ↔
    ∀ x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj,
      f.hom.app (op ((GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.p.obj x))
        (coarseValue B hZ K hK g hg x) = namedValue B hZ K hK g hg W H x := by
  constructor
  · rintro rfl
    exact factorization_sections B hZ K hK g hg W H
  · intro h
    exact factorMap_unique B hZ K hK g hg W H f
      ((factorization_iff_sections B hZ K hK g hg W H f).mpr h)

end M9Native.GenusNineCoarseCategoricalFactorization
