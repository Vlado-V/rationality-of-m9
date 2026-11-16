module

public import M9StacksIntegration.StandaloneCoefficientFamilyTransport

/-! Literal all-original-family classifiers and categorical coarse
universality under a genuine isomorphism of coefficient bases. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open M9StacksIntegration.AllTestOriginalFamilyCategory

universe u

namespace M9Native.StandaloneCoefficientClassifierTransport

open StandaloneCoefficientFamilyTransport

variable {K L : Type u} [Field K] [Field L]
    (e : Spec (.of K) ≅ Spec (.of L))

/-- A classifier on every original test is transported using the actual
inverse family functor, including nonschematic total spaces. -/
def classifierForward {g : ℕ} {M : M9StandaloneDraft.Presheaves K}
    (c : M9StandaloneDraft.Classifier K g M) :
    M9StandaloneDraft.Classifier L g (presheafForward e M) where
  value T F := c.value ((backward e).obj T) (familyBackward e T F)
  naturality := by
    intro T U a F G r hcart
    exact c.naturality ((backward e).obj T) ((backward e).obj U) ((backward e).map a)
      (familyBackward e T F) (familyBackward e U G) (presheafForwardMap e.symm r)
      (cartesianOver_forward e.symm r G.projection F.projection a hcart)

/-- The presheaf unit is the actual inverse of the original slice unit. -/
theorem presheaf_unit_app {M : M9StandaloneDraft.Presheaves K}
    (T : M9StandaloneDraft.Schemes K) (x : M.obj (op T)) :
    ((presheafEquivalence e).unitIso.app M).hom.app (op T) x =
      M.map (sliceUnitIso e T).inv.op x := rfl

/-- The presheaf counit is the actual inverse of the original slice counit. -/
theorem presheaf_counit_app {N : M9StandaloneDraft.Presheaves L}
    (T : M9StandaloneDraft.Schemes L)
    (x : N.obj (op ((forward e).obj ((backward e).obj T)))) :
    ((presheafEquivalence e).counitIso.app N).hom.app (op T) x =
      N.map (sliceCounitIso e T).inv.op x := rfl

/-- Roundtrip classifier values follow from the actual Cartesian family
unit, rather than a supplied comparison of moduli problems. -/
theorem classifier_unit_value {g : ℕ} {M : M9StandaloneDraft.Presheaves K}
    (c : M9StandaloneDraft.Classifier K g M)
    (T : M9StandaloneDraft.Schemes K) (F : M9StandaloneDraft.Family K T g) :
    M.map (sliceUnitIso e T).inv.op (c.value T F) =
      (classifierForward e c).value ((forward e).obj T) (familyForward e T F) := by
  let a := ((curveUnitIso e g).app (⟨T, F⟩ : CurveObject K g)).inv
  exact c.naturality T ((backward e).obj ((forward e).obj T)) a.baseMap F
    (familyBackward e ((forward e).obj T) (familyForward e T F)) a.totalMap a.cartesian

/-- The inverse family roundtrip is compared with every original family
by its actual Cartesian counit. -/
theorem classifier_counit_value {g : ℕ} {N : M9StandaloneDraft.Presheaves L}
    (d : M9StandaloneDraft.Classifier L g N)
    (T : M9StandaloneDraft.Schemes L) (F : M9StandaloneDraft.Family L T g) :
    N.map (sliceCounitIso e T).inv.op
        ((classifierForward e.symm d).value ((backward e).obj T) (familyBackward e T F)) =
      d.value T F := by
  let a := ((curveCounitIso e g).app (⟨T, F⟩ : CurveObject L g)).inv
  exact d.naturality ((forward e).obj ((backward e).obj T)) T a.baseMap
    (familyForward e ((backward e).obj T) (familyBackward e T F)) F a.totalMap a.cartesian

/-- Full categorical universality is transported against every algebraic
space target, using the genuine inverse Space and Family functors. -/
theorem isCategorical_forward {g : ℕ} {M : M9StandaloneDraft.Presheaves K}
    (c : M9StandaloneDraft.Classifier K g M) (hc : M9StandaloneDraft.IsCategorical K c) :
    M9StandaloneDraft.IsCategorical L (classifierForward e c) := by
  intro W d
  obtain ⟨f, hf, hu⟩ := hc (spaceBackward e W) (classifierForward e.symm d)
  let adj := (presheafEquivalence e).toAdjunction
  refine ⟨(adj.homEquiv M W.obj).symm f, ?_, ?_⟩
  · intro T F
    change ((presheafEquivalence e).counitIso.app W.obj).hom.app (op T)
      (f.app (op ((backward e).obj T))
        (c.value ((backward e).obj T) (familyBackward e T F))) = d.value T F
    rw [presheaf_counit_app, hf]
    exact classifier_counit_value e d T F
  · intro f' hf'
    apply (adj.homEquiv M W.obj).injective
    rw [Equiv.apply_symm_apply]
    apply hu (adj.homEquiv M W.obj f')
    intro T F
    change f'.app (op ((forward e).obj T))
      (((presheafEquivalence e).unitIso.app M).hom.app (op T) (c.value T F)) =
      (classifierForward e.symm d).value T F
    rw [presheaf_unit_app, classifier_unit_value]
    exact hf' ((forward e).obj T) (familyForward e T F)

end M9Native.StandaloneCoefficientClassifierTransport
