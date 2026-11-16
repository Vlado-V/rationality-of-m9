module

public import M9StacksIntegration.ParameterFamilyDeformation
public import M9StacksIntegration.SchemeMorphismSourceObstruction

/-!
# An actual family of morphisms gives original morphism deformations

Both endpoints are the literal pulled families. The special-fibre maps
are the ones of `ParameterFamilyDeformation`; their compatibility derives
the cartesian arrow to the original special-fibre morphism.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Deformation
open Deformation.Examples

universe u

namespace M9Native.ParameterMorphismDeformation

variable {k : Type u} [Field k] {X Y T : Scheme.{u}}
  (p : X ⟶ T) [Flat p] (q : Y ⟶ T) [Flat q]
  (h : X ⟶ Y) (hh : h ≫ q = p) (i : Spec (.of k) ⟶ T)

/-- The original family morphism after an actual change of parameter. -/
def pulledMap {Z : Scheme.{u}} (a : Z ⟶ T) : pullback p a ⟶ pullback q a :=
  pullback.lift (pullback.fst p a ≫ h) (pullback.snd p a) (by
    rw [Category.assoc, hh]
    exact pullback.condition)

omit [Flat p] [Flat q] in
/-- Its map to the parameter is the original second projection. -/
theorem pulledMap_toBase {Z : Scheme.{u}} (a : Z ⟶ T) :
    pulledMap p q h hh a ≫ pullback.snd q a = pullback.snd p a :=
  pullback.lift_snd _ _ _

omit [Flat p] [Flat q] in
/-- Its map to the original target is the literal original family morphism. -/
theorem pulledMap_toFamily {Z : Scheme.{u}} (a : Z ⟶ T) :
    pulledMap p q h hh a ≫ pullback.fst q a = pullback.fst p a ≫ h :=
  pullback.lift_fst _ _ _

/-- Pullback of the actual family morphism to the specified Artinian test. -/
def family (A : ArtinianLocalAlgCat.{u, u, u} k k) (a : baseSpec A ⟶ T) :
    SchemeMorphismFamily.{u, u} k k where
  base := A
  source := pullback p a
  target := pullback q a
  morphism := pulledMap p q h hh a
  sourceToBase := pullback.snd p a
  targetToBase := pullback.snd q a
  over_base := pulledMap_toBase p q h hh a
  source_flat := inferInstance
  target_flat := inferInstance

/-- The original source and target special-fibre maps respect the actual morphism. -/
theorem specialMap_compat (A : ArtinianLocalAlgCat.{u, u, u} k k)
    (a : baseSpec A ⟶ T) (ha : residueSpecMap A ≫ a = i) :
    (ParameterFamilyDeformation.deformation p i A a ha).specialMap ≫
        pulledMap p q h hh a =
      pulledMap p q h hh i ≫
        (ParameterFamilyDeformation.deformation q i A a ha).specialMap := by
  apply pullback.hom_ext
  · rw [Category.assoc, pulledMap_toFamily, ← Category.assoc,
      ParameterFamilyDeformation.specialMap_toFamily,
      Category.assoc, ParameterFamilyDeformation.specialMap_toFamily,
      pulledMap_toFamily]
  · rw [Category.assoc, pulledMap_toBase,
      ParameterFamilyDeformation.specialMap_toBase,
      Category.assoc, ParameterFamilyDeformation.specialMap_toBase,
      ← Category.assoc, pulledMap_toBase]

/-- A genuine native deformation of the original special-fibre morphism. -/
def deformation (A : ArtinianLocalAlgCat.{u, u, u} k k)
    (a : baseSpec A ⟶ T) (ha : residueSpecMap A ≫ a = i) :
    schemeMorphismDeformationCategory (Λ := k)
      (pulledMap p q h hh i) (pullback.snd p i) (pullback.snd q i)
      (pulledMap_toBase p q h hh i) :=
  Over.mk
    ({ base := (isTerminal_residueFieldBase (Λ := k) (k := k)).from A
       source := (ParameterFamilyDeformation.deformation p i A a ha).specialMap
       target := (ParameterFamilyDeformation.deformation q i A a ha).specialMap
       source_pullback := by
         refine IsPullback.of_right (h₂₂ := pullback.snd q a) ?_
           (specialMap_compat p q h hh i A a ha).symm
           (ParameterFamilyDeformation.deformation q i A a ha).specialCartesian.flip
         change IsPullback
           (pulledMap p q h hh i ≫ pullback.snd q i)
           (ParameterFamilyDeformation.deformation p i A a ha).specialMap
           (residueSpecMap A) (pulledMap p q h hh a ≫ pullback.snd q a)
         rw [pulledMap_toBase, pulledMap_toBase]
         exact (ParameterFamilyDeformation.deformation p i A a ha).specialCartesian.flip
       target_pullback := by
         rw [baseSpecMap_eq_residueSpecMap]
         exact (ParameterFamilyDeformation.deformation q i A a ha).specialCartesian } :
      family p q h hh A a ⟶
        schemeMorphismFamilySpecialFiber (Λ := k)
          (pulledMap p q h hh i) (pullback.snd p i) (pullback.snd q i)
          (pulledMap_toBase p q h hh i))

/-- The original source-forgetting functor returns exactly the original pulled family. -/
theorem sourceForgetful_obj (A : ArtinianLocalAlgCat.{u, u, u} k k)
    (a : baseSpec A ⟶ T) (ha : residueSpecMap A ≫ a = i) :
    (schemeMorphismSourceForgetful (Λ := k)
      (pulledMap p q h hh i) (pullback.snd p i) (pullback.snd q i)
      (pulledMap_toBase p q h hh i)).obj (deformation p q h hh i A a ha) =
      ParameterFamilyDeformation.deformation p i A a ha := rfl

/-- The target-forgetting functor likewise retains the literal pulled target family. -/
theorem targetForgetful_obj (A : ArtinianLocalAlgCat.{u, u, u} k k)
    (a : baseSpec A ⟶ T) (ha : residueSpecMap A ≫ a = i) :
    (schemeMorphismTargetForgetful (Λ := k)
      (pulledMap p q h hh i) (pullback.snd p i) (pullback.snd q i)
      (pulledMap_toBase p q h hh i)).obj (deformation p q h hh i A a ha) =
      ParameterFamilyDeformation.deformation q i A a ha := rfl

/-- The morphism deformation in the exact original fibre over its actual base. -/
def fibreObject (A : ArtinianLocalAlgCat.{u, u, u} k k)
    (a : baseSpec A ⟶ T) (ha : residueSpecMap A ≫ a = i) :
    (schemeMorphismDeformationCategoryProjection (Λ := k)
      (pulledMap p q h hh i) (pullback.snd p i) (pullback.snd q i)
      (pulledMap_toBase p q h hh i)).Fiber A :=
  ⟨deformation p q h hh i A a ha, rfl⟩

end M9Native.ParameterMorphismDeformation
