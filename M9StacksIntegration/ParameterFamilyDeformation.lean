module

public import M9StacksIntegration.StandardSchemeTangent

/-!
# An actual parameter family pulled back to an Artinian pointed test

The deformation below is built from the original flat scheme morphism and
its actual fibre. Its special-fibre map is the canonical pullback lift;
the proof of cartesianness uses the original two pullback squares.
Change of the Artinian test is an actual cartesian arrow in the native
scheme deformation category.

This extends the base-change construction of the pinned native
`StacksFrontier.Deformation.Examples.Geometric.SchemesCofibered`
(Stacks 0DY7), without modifying that source or supplying a deformation
class or a Kodaira--Spencer comparison as a hypothesis.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Deformation
open Deformation.Examples

universe u

namespace M9Native.ParameterFamilyDeformation

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  {X T : Scheme.{u}} (p : X ⟶ T) [Flat p] (i : Spec (.of k) ⟶ T)

/-- The original scheme-theoretic fibre over the specified field point. -/
abbrev fibre : Over (Spec (.of k)) := Over.mk (pullback.snd p i)

/-- Pullback of the actual family along a pointed Artinian test. -/
def deformation (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (a : baseSpec A ⟶ T) (ha : residueSpecMap A ≫ a = i) :
    SchemeDeformationCategory (Λ := Λ) (k := k) (fibre p i) where
  base := A
  scheme := pullback p a
  toBase := pullback.snd p a
  flat := inferInstance
  specialMap := pullback.lift (pullback.fst p i)
    (pullback.snd p i ≫ residueSpecMap A) (by
      rw [Category.assoc, ha]
      exact pullback.condition)
  specialCartesian := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback p a)
    rw [pullback.lift_fst, ha]
    exact IsPullback.of_hasPullback p i

/-- The native deformation retains the literal total-space fibre product. -/
theorem deformation_scheme (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (a : baseSpec A ⟶ T) (ha : residueSpecMap A ≫ a = i) :
    (deformation p i A a ha).scheme = pullback p a := rfl

/-- Its actual structure map is the second original pullback projection. -/
theorem deformation_toBase (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (a : baseSpec A ⟶ T) (ha : residueSpecMap A ≫ a = i) :
    (deformation p i A a ha).toBase = pullback.snd p a := rfl

/-- The special-fibre identification retains the original map to the family. -/
theorem specialMap_toFamily (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (a : baseSpec A ⟶ T) (ha : residueSpecMap A ≫ a = i) :
    (deformation p i A a ha).specialMap ≫ pullback.fst p a = pullback.fst p i :=
  pullback.lift_fst _ _ _

/-- The special-fibre base map is exactly the original residue-field map. -/
theorem specialMap_toBase (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (a : baseSpec A ⟶ T) (ha : residueSpecMap A ≫ a = i) :
    (deformation p i A a ha).specialMap ≫ pullback.snd p a =
      pullback.snd p i ≫ residueSpecMap A :=
  pullback.lift_snd _ _ _

/-- The deformation as an object of the exact native fibre over `A`. -/
def fibreObject (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (a : baseSpec A ⟶ T) (ha : residueSpecMap A ≫ a = i) :
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (fibre p i)).Fiber A :=
  ⟨deformation p i A a ha, rfl⟩

/-- Actual base change of pointed parameter tests induces a genuine native
cartesian deformation arrow, with the original special fibre fixed. -/
def changeTest {A B : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (a : baseSpec A ⟶ T) (ha : residueSpecMap A ≫ a = i)
    (b : baseSpec B ⟶ T) (hb : residueSpecMap B ≫ b = i)
    (g : A ⟶ B) (hg : baseSpecMap g ≫ a = b) :
    deformation p i A a ha ⟶ deformation p i B b hb where
  base := g
  map := pullback.lift (pullback.fst p b)
    (pullback.snd p b ≫ baseSpecMap g) (by
      rw [Category.assoc, hg]
      exact pullback.condition)
  cartesian := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback p a)
    rw [pullback.lift_fst, hg]
    exact IsPullback.of_hasPullback p b
  special_compat := by
    apply pullback.hom_ext
    · simp only [deformation, Category.assoc, pullback.lift_fst]
    · simp only [deformation, Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, pullback.lift_snd, Category.assoc,
        residueSpecMap_naturality]

/-- No change of the native Artinian base is hidden in this arrow. -/
theorem changeTest_base {A B : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (a : baseSpec A ⟶ T) (ha : residueSpecMap A ≫ a = i)
    (b : baseSpec B ⟶ T) (hb : residueSpecMap B ≫ b = i)
    (g : A ⟶ B) (hg : baseSpecMap g ≫ a = b) :
    (changeTest p i a ha b hb g hg).base = g := rfl

end M9Native.ParameterFamilyDeformation
