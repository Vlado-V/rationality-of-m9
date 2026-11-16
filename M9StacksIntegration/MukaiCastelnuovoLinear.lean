module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic

/-!
# The four-section case of Castelnuovo's trick

This file proves the linear algebra behind Mukai Proposition 3.2 in the
rank-two case used in Proposition 5.3. Six coordinates are the actual
minors of a pair of four-dimensional vectors. The Plücker equation and
its converse are proved explicitly; a kernel of dimension at least two
meets that equation over an algebraically closed field.

No decomposable-kernel conclusion is assumed. The sheaf-theoretic map to
which this criterion will be applied is constructed separately by native
exterior evaluation.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1000000

universe u v

namespace M9Native.MukaiCastelnuovoLinear

variable {K : Type u} [Field K]

/-- The six ordered `2 × 2` minors, in order `01,02,03,12,13,23`. -/
def wedgeCoordinates (a b : Fin 4 → K) : Fin 6 → K :=
  ![a 0 * b 1 - a 1 * b 0,
    a 0 * b 2 - a 2 * b 0,
    a 0 * b 3 - a 3 * b 0,
    a 1 * b 2 - a 2 * b 1,
    a 1 * b 3 - a 3 * b 1,
    a 2 * b 3 - a 3 * b 2]

/-- The actual Plücker equation for `Gr(2,4)`. -/
def plucker (x : Fin 6 → K) : K := x 0 * x 5 - x 1 * x 4 + x 2 * x 3

theorem plucker_wedgeCoordinates (a b : Fin 4 → K) :
    plucker (wedgeCoordinates a b) = 0 := by
  simp [plucker, wedgeCoordinates]
  ring

/-- A nonzero minor certifies linear independence of the original pair. -/
theorem linearIndependent_of_wedgeCoordinates_ne_zero {a b : Fin 4 → K}
    (h : wedgeCoordinates a b ≠ 0) : LinearIndependent K ![a, b] := by
  rw [linearIndependent_fin2]
  constructor
  · intro hb
    change b = 0 at hb
    apply h
    ext i
    fin_cases i <;> simp [wedgeCoordinates, hb]
  · intro t ht
    apply h
    have ht' : a = t • b := ht.symm
    ext i
    fin_cases i <;> simp [wedgeCoordinates, ht', Pi.smul_apply] <;> ring

/-- Every nonzero solution of the Plücker equation is the actual wedge
of an independent pair. Each of the six possible pivot minors is covered. -/
theorem exists_pair_of_plucker_zero {x : Fin 6 → K}
    (hx : x ≠ 0) (hP : plucker x = 0) :
    ∃ a b : Fin 4 → K, LinearIndependent K ![a, b] ∧ wedgeCoordinates a b = x := by
  have hP' : x 0 * x 5 - x 1 * x 4 + x 2 * x 3 = 0 := hP
  suffices ∃ a b : Fin 4 → K, wedgeCoordinates a b = x by
    obtain ⟨a,b,hab⟩ := this
    exact ⟨a,b,linearIndependent_of_wedgeCoordinates_ne_zero (hab ▸ hx),hab⟩
  by_cases h0 : x 0 ≠ 0
  · refine ⟨![1,0,-x 3 / x 0,-x 4 / x 0], ![0,x 0,x 1,x 2], ?_⟩
    ext i
    fin_cases i <;> simp [wedgeCoordinates] <;> field_simp
    all_goals grind
  by_cases h1 : x 1 ≠ 0
  · refine ⟨![1,x 3 / x 1,0,-x 5 / x 1], ![0,x 0,x 1,x 2], ?_⟩
    ext i
    fin_cases i <;> simp [wedgeCoordinates] <;> field_simp
    all_goals grind
  by_cases h2 : x 2 ≠ 0
  · refine ⟨![1,x 4 / x 2,x 5 / x 2,0], ![0,x 0,x 1,x 2], ?_⟩
    ext i
    fin_cases i <;> simp [wedgeCoordinates] <;> field_simp
    all_goals grind
  by_cases h3 : x 3 ≠ 0
  · refine ⟨![x 1 / x 3,1,0,-x 5 / x 3], ![-x 0,0,x 3,x 4], ?_⟩
    ext i
    fin_cases i <;> simp [wedgeCoordinates] <;> field_simp
    all_goals grind
  by_cases h4 : x 4 ≠ 0
  · refine ⟨![x 2 / x 4,1,x 5 / x 4,0], ![-x 0,0,x 3,x 4], ?_⟩
    ext i
    fin_cases i <;> simp [wedgeCoordinates] <;> field_simp
    all_goals grind
  have h5 : x 5 ≠ 0 := by
    intro h5
    apply hx
    ext i
    fin_cases i <;> simp_all
  refine ⟨![x 2 / x 5,x 4 / x 5,1,0], ![-x 1,-x 3,0,x 5], ?_⟩
  ext i
  fin_cases i <;> simp [wedgeCoordinates] <;> field_simp
  all_goals grind

/-- The polar coefficient of the Plücker quadratic. This expression is
valid in every characteristic. -/
def pluckerCross (x y : Fin 6 → K) : K :=
  x 0 * y 5 + y 0 * x 5 - x 1 * y 4 - y 1 * x 4 + x 2 * y 3 + y 2 * x 3

theorem plucker_add_smul (x y : Fin 6 → K) (t : K) :
    plucker (x + t • y) = plucker x + pluckerCross x y * t + plucker y * t ^ 2 := by
  simp only [plucker, pluckerCross, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Any vector subspace of the six Plücker coordinates of dimension at
least two contains a nonzero decomposable vector over an algebraically
closed field. The root is obtained from the actual binary quadratic. -/
theorem exists_plucker_zero_in_submodule [IsAlgClosed K]
    (U : Submodule K (Fin 6 → K)) (hU : 2 ≤ Module.finrank K U) :
    ∃ x : Fin 6 → K, x ∈ U ∧ x ≠ 0 ∧ plucker x = 0 := by
  obtain ⟨s, hs⟩ := exists_linearIndependent_of_le_finrank hU
  let x : Fin 6 → K := s 0
  let y : Fin 6 → K := s 1
  have hxy : LinearIndependent K ![x, y] := by
    have hi := hs.map' U.subtype (by simp)
    convert hi using 1
    ext i
    fin_cases i <;> rfl
  have hy : y ≠ 0 := (linearIndependent_fin2.mp hxy).1
  by_cases hP : plucker y = 0
  · exact ⟨y, (s 1).property, hy, hP⟩
  let p : Polynomial K := Polynomial.C (plucker x) + Polynomial.C (pluckerCross x y) *
    Polynomial.X + Polynomial.C (plucker y) * Polynomial.X ^ 2
  have hp2 : p.coeff 2 = plucker y := by simp [p]
  have hp : p.degree ≠ 0 := by
    intro hd
    have hc := congrArg (fun q : Polynomial K => q.coeff 2)
      (Polynomial.eq_C_of_degree_eq_zero hd)
    simp only [Polynomial.coeff_C, OfNat.ofNat_ne_zero, ite_false] at hc
    exact hP (hp2.symm.trans hc)
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_root p hp
  refine ⟨x + t • y, U.add_mem (s 0).property (U.smul_mem t (s 1).property), ?_, ?_⟩
  · intro hz
    apply (linearIndependent_fin2.mp hxy).2 (-t)
    change (-t) • y = x
    have he : x = -(t • y) := eq_neg_of_add_eq_zero_left hz
    simpa only [neg_smul] using he.symm
  · rw [plucker_add_smul]
    simpa only [Polynomial.IsRoot, p, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow] using ht

/-- A linear map from the actual six minor coordinates to a vector space
of dimension at most four kills the minors of an independent pair. -/
theorem exists_independent_pair_zero_minors [IsAlgClosed K]
    {W : Type v} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (L : (Fin 6 → K) →ₗ[K] W) (hW : Module.finrank K W ≤ 4) :
    ∃ a b : Fin 4 → K, LinearIndependent K ![a, b] ∧ L (wedgeCoordinates a b) = 0 := by
  have hker : 2 ≤ Module.finrank K L.ker := by
    have hsum := L.finrank_range_add_finrank_ker
    have hrange := Submodule.finrank_le L.range
    have hdim : Module.finrank K (Fin 6 → K) = 6 := by simp
    omega
  obtain ⟨x, hxker, hx, hP⟩ := exists_plucker_zero_in_submodule L.ker hker
  obtain ⟨a,b,hab,hw⟩ := exists_pair_of_plucker_zero hx hP
  refine ⟨a,b,hab, ?_⟩
  rw [hw]
  exact hxker

section AlternatingEvaluation

variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type*} [AddCommGroup W] [Module K W]

omit [AddCommGroup V] in
private theorem update_pair_last (a b c : V) :
    Function.update ![a,b] 1 c = ![a,c] := by
  ext i
  fin_cases i <;> rfl

/-- An alternating two-variable map, written as the corresponding actual
bilinear map. -/
def asBilinear (B : V [⋀^Fin 2]→ₗ[K] W) : V →ₗ[K] V →ₗ[K] W where
  toFun a :=
    { toFun := fun b => B ![a,b]
      map_add' b c := by
        simpa only [update_pair_last] using B.map_update_add ![a,0] 1 b c
      map_smul' t b := by
        simpa only [update_pair_last, RingHom.id_apply] using
          B.map_update_smul ![a,0] 1 t b }
  map_add' a c := by
    ext b
    exact B.map_vecCons_add ![b] a c
  map_smul' t a := by
    ext b
    exact B.map_vecCons_smul ![b] t a

@[simp] theorem asBilinear_apply (B : V [⋀^Fin 2]→ₗ[K] W) (a b : V) :
    asBilinear B a b = B ![a,b] := rfl

theorem alternating_pair_diag (B : V [⋀^Fin 2]→ₗ[K] W) (a : V) :
    B ![a,a] = 0 :=
  B.map_eq_zero_of_eq ![a,a] (i := 0) (j := 1) rfl (by decide)

theorem alternating_pair_swap (B : V [⋀^Fin 2]→ₗ[K] W) (a b : V) :
    B ![a,b] = -B ![b,a] := by
  have h := alternating_pair_diag B (a + b)
  change asBilinear B (a + b) (a + b) = 0 at h
  simp only [map_add, LinearMap.add_apply, asBilinear_apply,
    alternating_pair_diag, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

/-- Evaluation of the six coordinate basis wedges. -/
def minorMap (B : (Fin 4 → K) [⋀^Fin 2]→ₗ[K] W) : (Fin 6 → K) →ₗ[K] W :=
  Fintype.linearCombination K
    ![B ![Pi.single 0 1,Pi.single 1 1],
      B ![Pi.single 0 1,Pi.single 2 1],
      B ![Pi.single 0 1,Pi.single 3 1],
      B ![Pi.single 1 1,Pi.single 2 1],
      B ![Pi.single 1 1,Pi.single 3 1],
      B ![Pi.single 2 1,Pi.single 3 1]]

theorem minorMap_wedgeCoordinates
    (B : (Fin 4 → K) [⋀^Fin 2]→ₗ[K] W) (a b : Fin 4 → K) :
    minorMap B (wedgeCoordinates a b) = B ![a,b] := by
  let e : Fin 4 → (Fin 4 → K) := fun i => Pi.single i 1
  have ha : a = ∑ i : Fin 4, a i • e i := by
    ext j
    simp [e, Pi.single_apply]
  have hb : b = ∑ i : Fin 4, b i • e i := by
    ext j
    simp [e, Pi.single_apply]
  have hd (i : Fin 4) : B ![e i,e i] = 0 := alternating_pair_diag B _
  have hs (i j : Fin 4) : B ![e j,e i] = -B ![e i,e j] :=
    alternating_pair_swap B _ _
  calc
    minorMap B (wedgeCoordinates a b) =
        ∑ i : Fin 4, ∑ j : Fin 4, (a i * b j) • B ![e i,e j] := by
      simp only [minorMap, Fintype.linearCombination_apply, Fin.sum_univ_six,
        Fin.sum_univ_four]
      dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
      rw [hd 0, hd 1, hd 2, hd 3, hs 0 1, hs 0 2, hs 0 3, hs 1 2, hs 1 3, hs 2 3]
      simp [wedgeCoordinates, e]
      module
    _ = asBilinear B a b := by
      conv_rhs => rw [ha, hb]
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
        Finset.smul_sum, smul_smul, asBilinear_apply]
      rw [Finset.sum_comm]
      simp only [mul_comm]
    _ = B ![a,b] := rfl

/-- Castelnuovo's rank-two criterion on an actual alternating evaluation
map: four independent sections and at most four determinant sections
force two independent sections whose determinant wedge vanishes. -/
theorem exists_independent_pair_zero_of_finrank [IsAlgClosed K]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (B : V [⋀^Fin 2]→ₗ[K] W)
    (hV : 4 ≤ Module.finrank K V) (hW : Module.finrank K W ≤ 4) :
    ∃ a b : V, LinearIndependent K ![a,b] ∧ B ![a,b] = 0 := by
  obtain ⟨s,hs⟩ := exists_linearIndependent_of_le_finrank hV
  let j := Fintype.linearCombination K s
  have hj : Function.Injective j :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp hs
  let B' := B.compLinearMap j
  obtain ⟨a,b,hab,hzero⟩ := exists_independent_pair_zero_minors (minorMap B') hW
  refine ⟨j a,j b,?_,?_⟩
  · convert hab.map' j (LinearMap.ker_eq_bot.mpr hj) using 1
    ext i
    fin_cases i <;> rfl
  · rw [minorMap_wedgeCoordinates] at hzero
    change B (fun i => j (![a,b] i)) = 0 at hzero
    convert hzero using 1
    congr 1
    ext i
    fin_cases i <;> rfl

end AlternatingEvaluation

end M9Native.MukaiCastelnuovoLinear
