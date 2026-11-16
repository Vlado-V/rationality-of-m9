module

public import StacksFrontier.Deformation.FormalObject.VersalEquivalence
public import StacksFrontier.Deformation.CofiberedPresentation.SmoothPresentation
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.Deformation.Schlessinger.VersalBijectiveDifferential
public import StacksFrontier.Deformation.Formal.VersalObject.IsomorphismClassesFiberEquivalence
public import StacksFrontier.Deformation.Cofibered.BasedEquivalenceFibre
public import StacksFrontier.Deformation.Artin.FiniteDimensional.TangentTransfer
public import StacksFrontier.Deformation.Examples.Linear.ContinuousRepresentationsDenseRestriction

/-!
# The actual hull differential under an actual equivalence over Artin algebras

The comparison is proved on the original fibre classes. The native point-class
formula for a lift from a formal level identifies the mapped class, and the
original equivalence on fibres supplies its bijectivity. No comparison of
formal deformations or of tangent spaces is an input.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory Deformation

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber

universe u uF vF uG vG

namespace M9Native.FormalHullEquivalence

variable {k : Type u} [Field k]
  {F : Type uF} [Category.{vF} F] {G : Type uG} [Category.{vG} G]
  {q : G ⥤ ArtinianLocalAlgCat.{u,u,u} k k}

/-- The levelwise formal image gives the original image of each actual fibre class. -/
theorem pointClass_map (Φ : F ⥤ G)
    (hp : IsCofiberedInGroupoids (Φ ⋙ q)) (hq : IsCofiberedInGroupoids q)
    (ξ : FormalObject (Φ ⋙ q)) (P : ChosenPushforwards (Φ ⋙ q))
    (Q : ChosenPushforwards q) (A : ArtinianLocalAlgCat.{u,u,u} k k)
    (a : (restrictedCoyoneda ξ.base).obj A) :
    pointClass hq ((formalObjectMapOfCompEq Φ rfl).obj ξ) Q A a =
      mapIsomorphismClasses hp hq (⟨Φ,rfl⟩ : BasedFunctor
        (BasedCategory.ofFunctor (Φ ⋙ q)) (BasedCategory.ofFunctor q)) A
        (pointClass hp ξ P A a) := by
  let η := (formalObjectMapOfCompEq Φ rfl).obj ξ
  let H := associatedMorphism hp ξ P
  let α := (restrictedCoyoneda ξ.base).elementsMk A a
  let φ : BasedFunctor (BasedCategory.ofFunctor (Φ ⋙ q)) (BasedCategory.ofFunctor q) := ⟨Φ,rfl⟩
  have hi : (Φ ⋙ q).IsHomLift (H.factor α) (H.pointInclusion α) :=
    associatedMorphism_pointInclusion_isHomLift ξ H α
  letI : (BasedCategory.ofFunctor (Φ ⋙ q)).p.IsHomLift (H.factor α) (H.pointInclusion α) := hi
  have hi' : q.IsHomLift (H.factor α) (Φ.map (H.pointInclusion α)) :=
    BasedFunctor.preserves_isHomLift φ (H.factor α) (H.pointInclusion α)
  have hx : q.obj (Φ.obj (H.toBasedFunctor.obj α)) = A := H.toBasedFunctor.w_obj α
  have hh := pointClass_of_lift hq η Q (H.level α) (H.factor α) hx
    (Φ.map (H.pointInclusion α)) hi'
  have ha : truncationPoint ξ.base (H.level α) ≫ artinianToComplete.map (H.factor α) = a := by
    apply CompleteLocalAlgCat.Hom.ext
    exact (H.factor_spec α).2.2
  change pointClass hq η Q A
    (truncationPoint ξ.base (H.level α) ≫ artinianToComplete.map (H.factor α)) = _ at hh
  rw [ha] at hh
  change pointClass hq η Q A a = mapIsomorphismClasses hp hq φ A
    (classOf (BasedCategory.ofFunctor (Φ ⋙ q)) hp ⟨H.toBasedFunctor.obj α,H.toBasedFunctor.w_obj α⟩)
  rw [mapIsomorphismClasses_classOf]
  exact hh

/-- An actual equivalence over the base preserves actual hull-differential bijectivity. -/
theorem hasBijectiveDifferential_map {p : F ⥤ ArtinianLocalAlgCat.{u,u,u} k k}
    (Φ : F ⥤ G) (hΦ : Φ ⋙ q = p) [Φ.IsEquivalence]
    (hp : IsCofiberedInGroupoids p) (hq : IsCofiberedInGroupoids q)
    (ξ : FormalObject p) (hξ : HasBijectiveDifferential hp ξ) :
    HasBijectiveDifferential hq ((formalObjectMapOfCompEq Φ hΦ).obj ξ) := by
  subst hΦ
  obtain ⟨P,hP⟩ := hξ
  let Q := chosenPushforwardsOfCofibered q hq
  let φ : BasedFunctor (BasedCategory.ofFunctor (Φ ⋙ q)) (BasedCategory.ofFunctor q) := ⟨Φ,rfl⟩
  letI : φ.toFunctor.IsEquivalence := inferInstanceAs (Φ.IsEquivalence)
  let A := artinianDualNumbers.{u,u,u} k k
  have hfull : (fiberFunctor φ A).Full := full_fiberFunctor φ A
  have hfaithful : (fiberFunctor φ A).Faithful := faithful_fiberFunctor φ A
  have hess : (fiberFunctor φ A).EssSurj := essSurj_fiberFunctor hp φ A
  have hbij := bijective_mapIsomorphismClasses_of_fiberEquivalence hp hq φ A hfull hfaithful hess
  refine ⟨Q,?_⟩
  letI : Algebra ξ.base k := (residueHom ξ.base).toRingHom.toAlgebra
  have he : derivationToTangent hq ((formalObjectMapOfCompEq Φ rfl).obj ξ) Q =
      mapIsomorphismClasses hp hq φ A ∘ derivationToTangent hp ξ P := by
    funext d
    change derivationToTangent hq ((formalObjectMapOfCompEq Φ rfl).obj ξ) Q d =
      mapIsomorphismClasses hp hq φ A (derivationToTangent hp ξ P d)
    rw [derivationToTangent_eq_pointClass,derivationToTangent_eq_pointClass]
    exact pointClass_map Φ hp hq ξ P Q A _
  rw [he]
  exact hbij.comp hP

/-- Faithfulness of the actual rigidified structure projection transports
along the actual equivalence over the base; it is not assumed on the target. -/
theorem faithful_target {p : F ⥤ ArtinianLocalAlgCat.{u,u,u} k k}
    (Φ : F ⥤ G) (hΦ : Φ ⋙ q = p) [Φ.IsEquivalence] [p.Faithful]
    (hp : IsCofiberedInGroupoids p) : q.Faithful := by
  let E := equivalenceOverOfCofibered hp Φ hΦ
  letI : E.inv.functor.IsEquivalence := E.isEquivalence_inv_functor
  have h : (E.inv.functor ⋙ p).Faithful := inferInstance
  exact E.inv.w ▸ h

end M9Native.FormalHullEquivalence
