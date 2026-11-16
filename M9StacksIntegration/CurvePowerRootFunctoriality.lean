module

public import M9StacksIntegration.CurvePowerFiniteTopPower
public import M9StacksIntegration.CurvePowerFiltrationRoots

/-!
# Ring-homomorphism transport of the finite moving-root calculation

These are identities for genuine ring maps. In particular the inverse
coefficients are transported through their proved finite recurrence;
no compatibility with an infinite inverse in an uncompleted subring
is required.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096

namespace M9Native.CurvePowerRootFunctoriality

open CurvePowerRootSums CurvePowerRootChern CurvePowerTopPower
open CurvePowerFiniteTopPower CurvePowerFiltrationRoots

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

theorem map_elementary (r : List R) (n : ℕ) :
    f (elementary r n) = elementary (r.map f) n := by
  induction r generalizing n with
  | nil => cases n <;> simp only [elementary, List.map_nil, map_zero, map_one]
  | cons a r ih =>
      cases n with
      | zero => simp only [elementary_zero, map_one]
      | succ n => simp only [elementary, List.map_cons, map_add, map_mul, ih]

theorem map_segreCoefficient (r : List R) (n : ℕ) :
    f (segreCoefficient r n) = segreCoefficient (r.map f) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp only [segreCoefficient_zero, map_one]
      | succ n =>
          rw [segreCoefficient_succ, segreCoefficient_succ, map_neg, map_sum]
          apply congrArg Neg.neg
          apply Finset.sum_congr rfl
          intro a ha
          by_cases h : a.2 < n + 1
          · simp only [h, ite_true, map_mul, map_elementary, ih a.2 h]
          · simp only [h, ite_false, map_zero]

theorem map_segreSchurDet (r : List R) :
    f (segreSchurMatrix r).det = (segreSchurMatrix (r.map f)).det := by
  rw [f.map_det]
  apply congrArg Matrix.det
  ext i j
  change f ((segreSchurMatrix r) i j) = (segreSchurMatrix (r.map f)) i j
  fin_cases i <;> fin_cases j <;>
    simp [segreSchurMatrix, map_segreCoefficient]

theorem map_extendZero {n : ℕ} (p : Fin n → R) :
    (fun i => f (extendZero p i)) = extendZero (fun i => f (p i)) := by
  funext i
  by_cases hi : i < n <;> simp only [extendZero, hi, dite_true, dite_false, map_zero]

theorem map_extendZero₂ {n : ℕ} (d : Fin n → Fin n → R) :
    (fun i j => f (extendZero₂ d i j)) = extendZero₂ (fun i j => f (d i j)) := by
  funext i j
  unfold extendZero₂
  by_cases hij : i < n ∧ j < n
  · rw [dite_eq_left hij, dite_eq_left hij]
  · rw [dite_eq_right hij, dite_eq_right hij, map_zero]

theorem map_boundary (d : ℕ → ℕ → R) :
    (fun n => f (boundary d n)) = boundary (fun i j => f (d i j)) := by
  funext n
  simp only [boundary, map_sum]

theorem map_nextRoots (n : ℕ) (r : List R) (p b : R) :
    (nextRoots n r p b).map f = nextRoots n (r.map f) (f p) (f b) := by
  simp only [nextRoots, List.map_cons, List.map_map, map_add, map_mul, map_natCast]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact f.map_sub a p

theorem map_roots (g : ℕ) (p b : ℕ → R) (n : ℕ) :
    (roots g p b n).map f = roots g (fun i => f (p i)) (fun i => f (b i)) n := by
  induction n with
  | zero => simp only [roots, List.map_replicate, map_zero]
  | succ n ih => rw [roots, map_nextRoots, ih, roots]

theorem map_pointSum (p : ℕ → R) (n : ℕ) :
    f (pointSum p n) = pointSum (fun i => f (p i)) n := by
  induction n with
  | zero => simp only [pointSum, map_zero]
  | succ n ih => rw [pointSum, map_add, ih, pointSum]

theorem map_graphQuotient (p : ℕ → R) (d : ℕ → ℕ → R) (ambient j : ℕ) :
    f (graphQuotient p d ambient j) =
      graphQuotient (fun i => f (p i)) (fun i j => f (d i j)) ambient j := by
  simp only [graphQuotient, map_add, map_neg, map_mul, map_ofNat, map_sum, map_pointSum]

end M9Native.CurvePowerRootFunctoriality
