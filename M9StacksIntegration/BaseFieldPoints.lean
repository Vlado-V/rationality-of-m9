module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Detecting native scheme emptiness on base-field points

A scheme locally of finite type over an algebraically closed field is
nonempty if and only if it has an actual rational point over that field.
The proof uses the native Jacobson-space theorem and the actual closed-
point/rational-point equivalence. No assertion about points over arbitrary
field extensions is assumed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.BaseFieldPoints

variable {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]

/-- A nonempty native scheme locally of finite type over the
algebraically closed base has an actual base-field rational point. -/
theorem exists_point [Nonempty X] :
    ∃ p : Spec (.of K) ⟶ X, p ≫ f = 𝟙 _ := by
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, hx⟩ := nonempty_inter_closedPoints
    (Z := (Set.univ : Set X)) Set.univ_nonempty isOpen_univ.isLocallyClosed
  exact ⟨pointOfClosedPoint f x hx.2, pointOfClosedPoint_comp f x hx.2⟩

/-- Under this actual finite-type hypothesis, base-field rational
points detect nonemptiness of the whole native scheme. -/
theorem nonempty_iff_exists_point :
    Nonempty X ↔ ∃ p : Spec (.of K) ⟶ X, p ≫ f = 𝟙 _ := by
  constructor
  · intro h
    let := h
    exact exists_point f
  · rintro ⟨p, _⟩
    exact ⟨p (IsLocalRing.closedPoint K)⟩

/-- Excluding actual rational points over the stated algebraically
closed base proves genuine emptiness; no extension-field premise is
needed. -/
theorem isEmpty_of_no_point
    (h : ∀ p : Spec (.of K) ⟶ X, p ≫ f ≠ 𝟙 _) : IsEmpty X := by
  refine ⟨fun x => ?_⟩
  let : Nonempty X := ⟨x⟩
  obtain ⟨p, hp⟩ := exists_point f
  exact h p hp

end M9Native.BaseFieldPoints
