module

public import M9StacksIntegration.CurvePowerTopPower

/-! Literal zero extensions of finite point/diagonal classes to the
natural-number families of the integral top-power calculation. These
are generic ring identities; their geometric realization is separate. -/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 300000

open scoped BigOperators

namespace M9Native.CurvePowerFiniteTopPower

open CurvePowerRootSums CurvePowerRootChern CurvePowerTopPower

variable {R : Type*} [CommRing R] {n : ℕ}

def extendZero (p : Fin n → R) (i : ℕ) : R :=
  if h : i < n then p ⟨i,h⟩ else 0

def extendZero₂ (β : Fin n → Fin n → R) (i j : ℕ) : R :=
  if h : i < n ∧ j < n then β ⟨i,h.1⟩ ⟨j,h.2⟩ else 0

@[simp] theorem extendZero_fin (p : Fin n → R) (i : Fin n) :
    extendZero p i.val = p i := by
  simp only [extendZero,dite_eq_left i.isLt]

@[simp] theorem extendZero₂_fin (β : Fin n → Fin n → R) (i j : Fin n) :
    extendZero₂ β i.val j.val = β i j := by
  simp only [extendZero₂,dite_eq_left (And.intro i.isLt j.isLt)]

theorem pointProduct_extendZero (p : Fin n → R) :
    pointProduct (extendZero p) n = ∏ i : Fin n, p i := by
  simpa only [pointProduct,extendZero_fin] using (Fin.prod_univ_eq_prod_range (extendZero p) n).symm

theorem extendZero_sq (p : Fin n → R) (hp : ∀ i, p i ^ 2 = 0) (i : ℕ) :
    extendZero p i ^ 2 = 0 := by
  by_cases hi : i < n
  · simpa only [extendZero,dite_eq_left hi] using hp ⟨i,hi⟩
  · simp [extendZero,hi]

theorem extendZero_left (p : Fin n → R) (β : Fin n → Fin n → R)
    (h : ∀ i j, i < j → p i * β i j = 0) (i j : ℕ) (hij : i < j) :
    extendZero p i * extendZero₂ β i j = 0 := by
  by_cases hj : j < n
  · have hi : i < n := lt_trans hij hj
    simpa only [extendZero,extendZero₂,dite_eq_left hi,dite_eq_left (And.intro hi hj)] using
      h ⟨i,hi⟩ ⟨j,hj⟩ hij
  · simp [extendZero₂,hj]

theorem extendZero_right (p : Fin n → R) (β : Fin n → Fin n → R)
    (h : ∀ i j, i < j → p j * β i j = 0) (i j : ℕ) (hij : i < j) :
    extendZero p j * extendZero₂ β i j = 0 := by
  by_cases hj : j < n
  · have hi : i < n := lt_trans hij hj
    simpa only [extendZero,extendZero₂,dite_eq_left hj,dite_eq_left (And.intro hi hj)] using
      h ⟨i,hi⟩ ⟨j,hj⟩ hij
  · simp [extendZero,extendZero₂,hj]

theorem extendZero_square (p : Fin n → R) (β : Fin n → Fin n → R)
    (h : ∀ i j, i < j → β i j ^ 2 = -18 * p i * p j) (i j : ℕ) (hij : i < j) :
    extendZero₂ β i j ^ 2 = -18 * extendZero p i * extendZero p j := by
  by_cases hj : j < n
  · have hi : i < n := lt_trans hij hj
    simpa only [extendZero,extendZero₂,dite_eq_left hi,dite_eq_left hj,dite_eq_left (And.intro hi hj)] using
      h ⟨i,hi⟩ ⟨j,hj⟩ hij
  · simp [extendZero,extendZero₂,hj]

theorem extendZero_cross (p : Fin n → R) (β : Fin n → Fin n → R)
    (h : ∀ i j l, i < j → j < l → β i l * β j l = p l * β i j)
    (i j l : ℕ) (hij : i < j) (hjl : j < l) :
    extendZero₂ β i l * extendZero₂ β j l = extendZero p l * extendZero₂ β i j := by
  by_cases hl : l < n
  · have hj : j < n := lt_trans hjl hl
    have hi : i < n := lt_trans hij hj
    simpa only [extendZero,extendZero₂,dite_eq_left hl,dite_eq_left (And.intro hi hl),
      dite_eq_left (And.intro hj hl),dite_eq_left (And.intro hi hj)] using
      h ⟨i,hi⟩ ⟨j,hj⟩ ⟨l,hl⟩ hij hjl
  · simp [extendZero,extendZero₂,hl]

/-- The finite nine-index local relations and actual normalized additive
trace imply the literal integral Schur trace after zero extension. -/
theorem segreSchur_trace_nine (τ : R →+ ℤ) (p : Fin 9 → R) (β : Fin 9 → Fin 9 → R)
    (hp : ∀ i, p i ^ 2 = 0)
    (hleft : ∀ i j, i < j → p i * β i j = 0)
    (hright : ∀ i j, i < j → p j * β i j = 0)
    (hsquare : ∀ i j, i < j → β i j ^ 2 = -18 * p i * p j)
    (hcross : ∀ i j l, i < j → j < l → β i l * β j l = p l * β i j)
    (hpoint : τ (∏ i : Fin 9, p i) = 1) :
    τ ((segreSchurMatrix (roots 9 (extendZero p) (boundary (extendZero₂ β)) 9)).det) = 15240960 := by
  apply movingRoots_segreSchur_trace_nine τ (extendZero p) (extendZero₂ β)
    (extendZero_sq p hp) (extendZero_left p β hleft) (extendZero_right p β hright)
    (extendZero_square p β hsquare) (extendZero_cross p β hcross)
  simpa only [pointProduct_extendZero] using hpoint

theorem segreSchur_ne_zero_nine (τ : R →+ ℤ) (p : Fin 9 → R) (β : Fin 9 → Fin 9 → R)
    (hp : ∀ i, p i ^ 2 = 0)
    (hleft : ∀ i j, i < j → p i * β i j = 0)
    (hright : ∀ i j, i < j → p j * β i j = 0)
    (hsquare : ∀ i j, i < j → β i j ^ 2 = -18 * p i * p j)
    (hcross : ∀ i j l, i < j → j < l → β i l * β j l = p l * β i j)
    (hpoint : τ (∏ i : Fin 9, p i) = 1) :
    (segreSchurMatrix (roots 9 (extendZero p) (boundary (extendZero₂ β)) 9)).det ≠ 0 := by
  intro he
  have ht := segreSchur_trace_nine τ p β hp hleft hright hsquare hcross hpoint
  rw [he,map_zero] at ht
  norm_num at ht

end M9Native.CurvePowerFiniteTopPower
