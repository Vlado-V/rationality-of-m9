module

public import M9StacksIntegration.StandaloneCoefficientClassifierTransport

/-! Genuine transport of coarse geometric points, retaining every original
extension field and deriving its coefficient action from the ring map. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open M9StacksIntegration.AllTestOriginalFamilyCategory

universe u

namespace M9Native.StandaloneCoefficientGeometricTransport

open StandaloneCoefficientFamilyTransport StandaloneCoefficientClassifierTransport

variable {K L : Type u} [Field K] [Field L]
    (e : Spec (.of K) ≅ Spec (.of L))

/-- Forward transport corrected to an exact prescribed original test. -/
def familyForwardAt {g : ℕ} (T : M9StandaloneDraft.Schemes L)
    (F : M9StandaloneDraft.Family K ((backward e).obj T) g) :
    M9StandaloneDraft.Family L T g :=
  M9StacksIntegration.AllTestFamilyPullback.pullbackFamily L
    (familyForward e ((backward e).obj T) F) (sliceCounitIso e T).inv

/-- The actual Cartesian recovery arrow uses the inverse family functor
and the genuine family unit. -/
def recoveryMap {g : ℕ} (T : M9StandaloneDraft.Schemes L)
    (F : M9StandaloneDraft.Family K ((backward e).obj T) g) :
    (⟨(backward e).obj T, familyBackward e T (familyForwardAt e T F)⟩ : CurveObject K g) ⟶
      (⟨(backward e).obj T, F⟩ : CurveObject K g) :=
  (curveFunctor e.symm g).map
    (pullbackMap L g
      (⟨(forward e).obj ((backward e).obj T),
        familyForward e ((backward e).obj T) F⟩ : CurveObject L g)
      (sliceCounitIso e T).inv) ≫
    ((curveUnitIso e g).app (⟨(backward e).obj T, F⟩ : CurveObject K g)).inv

/-- Recovery is over the identity of the entire original test scheme. -/
theorem recoveryMap_base {g : ℕ} (T : M9StandaloneDraft.Schemes L)
    (F : M9StandaloneDraft.Family K ((backward e).obj T) g) :
    (recoveryMap e T F).baseMap = 𝟙 ((backward e).obj T) := by
  apply Over.OverMorphism.ext
  change 𝟙 T.left ≫ 𝟙 T.left = 𝟙 T.left
  simp

/-- Literal classifier values of every original family are recovered. -/
theorem classifierForward_recovery {g : ℕ} {M : M9StandaloneDraft.Presheaves K}
    (c : M9StandaloneDraft.Classifier K g M) (T : M9StandaloneDraft.Schemes L)
    (F : M9StandaloneDraft.Family K ((backward e).obj T) g) :
    (classifierForward e c).value T (familyForwardAt e T F) =
      c.value ((backward e).obj T) F := by
  let a := recoveryMap e T F
  have h := c.naturality ((backward e).obj T) ((backward e).obj T) a.baseMap
    F (familyBackward e T (familyForwardAt e T F)) a.totalMap a.cartesian
  rw [recoveryMap_base] at h
  change c.value ((backward e).obj T) (familyBackward e T (familyForwardAt e T F)) =
    c.value ((backward e).obj T) F
  simpa only [op_id, CategoryTheory.Functor.map_id, types_id_apply] using h.symm

/-- The geometric assertion at one entire original test scheme. -/
def GeometricAt {g : ℕ} {M : M9StandaloneDraft.Presheaves K}
    (c : M9StandaloneDraft.Classifier K g M) (T : M9StandaloneDraft.Schemes K) : Prop :=
  Function.Surjective (c.value T) ∧
    ∀ F G : M9StandaloneDraft.Family K T g,
      c.value T F = c.value T G ↔ M9StandaloneDraft.FamilyIsomorphic K F G

theorem geometricAt_forward {g : ℕ} {M : M9StandaloneDraft.Presheaves K}
    (c : M9StandaloneDraft.Classifier K g M) (T : M9StandaloneDraft.Schemes L)
    (h : GeometricAt c ((backward e).obj T)) :
    GeometricAt (classifierForward e c) T := by
  constructor
  · intro x
    obtain ⟨F, hF⟩ := h.1 x
    exact ⟨familyForwardAt e T F, (classifierForward_recovery e c T F).trans hF⟩
  · intro F G
    exact (h.2 (familyBackward e T F) (familyBackward e T G)).trans
      (familyIsomorphic_forward_iff e.symm T F G)

/-- The spectrum isomorphism is constructed from the coefficient ring map. -/
def coefficientSpecIso (E : K ≃+* L) : Spec (.of K) ≅ Spec (.of L) :=
  (Scheme.Spec.mapIso E.toCommRingCatIso.op).symm

/-- Every original extension field is retained, with its K-action derived
by composition with the actual coefficient map. -/
abbrev extensionAlgebra (E : K ≃+* L) (A : Type u) [Field A] [Algebra L A] : Algebra K A :=
  ((algebraMap L A).comp E.toRingHom).toAlgebra

theorem fieldPoint_backward_eq (E : K ≃+* L) (A : Type u) [Field A] [Algebra L A] :
    let _ := extensionAlgebra E A
    (backward (coefficientSpecIso E)).obj (M9StandaloneDraft.FieldPoint L A) =
      M9StandaloneDraft.FieldPoint K A := by
  let _ := extensionAlgebra E A
  change Over.mk
    (Spec.map (CommRingCat.ofHom (algebraMap L A)) ≫
      Spec.map E.toCommRingCatIso.hom) =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K A)))
  rw [← Spec.map_comp]
  rfl

/-- All algebraically closed extension fields and exact unpointed-family
isomorphism classes are retained by the derived transport. -/
theorem isGeometric_forward (E : K ≃+* L) {g : ℕ}
    {M : M9StandaloneDraft.Presheaves K} (c : M9StandaloneDraft.Classifier K g M)
    (hc : M9StandaloneDraft.IsGeometric K c) :
    M9StandaloneDraft.IsGeometric L (classifierForward (coefficientSpecIso E) c) := by
  intro A hA aL hclosed
  let _ := extensionAlgebra E A
  have h : GeometricAt c
      ((backward (coefficientSpecIso E)).obj (M9StandaloneDraft.FieldPoint L A)) := by
    rw [fieldPoint_backward_eq]
    exact hc A
  exact geometricAt_forward (coefficientSpecIso E) c (M9StandaloneDraft.FieldPoint L A) h

/-- Genuine full coarse moduli is preserved, including all algebraic-space
targets and every original geometric extension field. -/
theorem isCoarse_forward (E : K ≃+* L) {g : ℕ}
    {M : M9StandaloneDraft.Presheaves K} (c : M9StandaloneDraft.Classifier K g M)
    (hc : M9StandaloneDraft.IsCoarse K c) :
    M9StandaloneDraft.IsCoarse L (classifierForward (coefficientSpecIso E) c) :=
  ⟨isCategorical_forward (coefficientSpecIso E) c hc.1,
    isGeometric_forward E c hc.2⟩

end M9Native.StandaloneCoefficientGeometricTransport
