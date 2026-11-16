module

public import M9StacksIntegration.MukaiCastelnuovoLinear

/-!
# Actual bivectors in dimension three

Every nonzero element of the actual second exterior power of a
three-dimensional vector space is the wedge of an independent pair.
The proof expands the three actual basis wedges and gives explicit
pairs for the possible pivot coordinates. It works over every field.

The exterior-power model is exactly the one used by `ExteriorEvaluation`.
The final corollaries turn nonvanishing on independent wedges into actual
injectivity and the consequent target-dimension bound. No geometric
nonvanishing premise is discharged in this pure linear-algebra leaf.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1000000

universe u v w

namespace M9Native.MukaiThreeDimensionalBivectors

variable {K : Type u} [Field K]

/-- The three ordered minors `01,02,12`. -/
def wedgeCoordinates (a b : Fin 3 → K) : Fin 3 → K :=
  ![a 0 * b 1 - a 1 * b 0,
    a 0 * b 2 - a 2 * b 0,
    a 1 * b 2 - a 2 * b 1]

/-- A nonzero actual minor makes the original pair independent. -/
theorem linearIndependent_of_wedgeCoordinates_ne_zero {a b : Fin 3 → K}
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

/-- Every nonzero three-coordinate bivector is obtained from an actual
independent pair. The first two cases use a nonzero pivot; the last is
supported on the `12` coordinate. -/
theorem exists_pair_of_coordinates_ne_zero {x : Fin 3 → K} (hx : x ≠ 0) :
    ∃ a b : Fin 3 → K, LinearIndependent K ![a, b] ∧ wedgeCoordinates a b = x := by
  suffices ∃ a b : Fin 3 → K, wedgeCoordinates a b = x by
    obtain ⟨a, b, hab⟩ := this
    exact ⟨a, b, linearIndependent_of_wedgeCoordinates_ne_zero (hab ▸ hx), hab⟩
  by_cases h0 : x 0 ≠ 0
  · refine ⟨![1, 0, -x 2 / x 0], ![0, x 0, x 1], ?_⟩
    ext i
    fin_cases i <;> simp [wedgeCoordinates, h0]
  have h0' : x 0 = 0 := not_ne_iff.mp h0
  by_cases h1 : x 1 ≠ 0
  · refine ⟨![1, x 2 / x 1, 0], ![0, 0, x 1], ?_⟩
    ext i
    fin_cases i <;> simp [wedgeCoordinates, h0', h1]
  have h1' : x 1 = 0 := not_ne_iff.mp h1
  refine ⟨![0, 1, 0], ![0, 0, x 2], ?_⟩
  ext i
  fin_cases i <;> simp [wedgeCoordinates, h0', h1']

/-- Linear combination of the actual exterior basis wedges. -/
def coordinateExpansion : (Fin 3 → K) →ₗ[K] (⋀[K]^2 (Fin 3 → K)) :=
  Fintype.linearCombination K
    ![exteriorPower.ιMulti K 2 ![Pi.single 0 1, Pi.single 1 1],
      exteriorPower.ιMulti K 2 ![Pi.single 0 1, Pi.single 2 1],
      exteriorPower.ιMulti K 2 ![Pi.single 1 1, Pi.single 2 1]]

/-- The coordinate expansion agrees with the actual canonical wedge,
proved by bilinear expansion and alternating signs. -/
theorem coordinateExpansion_wedgeCoordinates (a b : Fin 3 → K) :
    coordinateExpansion (wedgeCoordinates a b) = exteriorPower.ιMulti K 2 ![a, b] := by
  let B := exteriorPower.ιMulti K 2 (M := Fin 3 → K)
  let e : Fin 3 → (Fin 3 → K) := fun i => Pi.single i 1
  have ha : a = ∑ i : Fin 3, a i • e i := by
    ext j
    simp [e, Pi.single_apply]
  have hb : b = ∑ i : Fin 3, b i • e i := by
    ext j
    simp [e, Pi.single_apply]
  have hd (i : Fin 3) : B ![e i, e i] = 0 :=
    MukaiCastelnuovoLinear.alternating_pair_diag B _
  have hs (i j : Fin 3) : B ![e j, e i] = -B ![e i, e j] :=
    MukaiCastelnuovoLinear.alternating_pair_swap B _ _
  calc
    coordinateExpansion (wedgeCoordinates a b) =
        ∑ i : Fin 3, ∑ j : Fin 3, (a i * b j) • B ![e i, e j] := by
      simp only [coordinateExpansion, Fintype.linearCombination_apply, Fin.sum_univ_three]
      dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ]
      rw [hd 0, hd 1, hd 2, hs 0 1, hs 0 2, hs 1 2]
      simp [wedgeCoordinates, B, e]
      module
    _ = MukaiCastelnuovoLinear.asBilinear B a b := by
      conv_rhs => rw [ha, hb]
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
        Finset.smul_sum, smul_smul, MukaiCastelnuovoLinear.asBilinear_apply]
      rw [Finset.sum_comm]
      simp only [mul_comm]
    _ = exteriorPower.ιMulti K 2 ![a, b] := rfl

/-- The three actual basis wedges span the actual second exterior
power. This uses the native exterior-power spanning theorem. -/
theorem coordinateExpansion_surjective :
    Function.Surjective (coordinateExpansion (K := K)) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← exteriorPower.ιMulti_span K 2 (Fin 3 → K)]
  apply Submodule.span_le.mpr
  rintro _ ⟨s, rfl⟩
  refine ⟨wedgeCoordinates (s 0) (s 1), ?_⟩
  have hs : ![s 0, s 1] = s := by
    ext i
    fin_cases i <;> rfl
  simpa only [hs] using coordinateExpansion_wedgeCoordinates (s 0) (s 1)

/-- Every nonzero actual bivector in `K³` is an actual wedge of an
independent pair, without a decomposability or Plücker premise. -/
theorem exists_independent_pair_of_ne_zero
    {z : ⋀[K]^2 (Fin 3 → K)} (hz : z ≠ 0) :
    ∃ a b : Fin 3 → K, LinearIndependent K ![a, b] ∧
      exteriorPower.ιMulti K 2 ![a, b] = z := by
  obtain ⟨x, hx⟩ := coordinateExpansion_surjective z
  have hx0 : x ≠ 0 := by
    intro h
    apply hz
    rw [← hx, h, map_zero]
  obtain ⟨a, b, hab, habx⟩ := exists_pair_of_coordinates_ne_zero hx0
  refine ⟨a, b, hab, ?_⟩
  rw [← coordinateExpansion_wedgeCoordinates, habx, hx]

section GeneralSpace

variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The same literal decomposition for every actual vector space of
dimension three, transported by an actual basis equivalence. -/
theorem exists_independent_pair_of_finrank_three
    (hV : Module.finrank K V = 3) {z : ⋀[K]^2 V} (hz : z ≠ 0) :
    ∃ a b : V, LinearIndependent K ![a, b] ∧ exteriorPower.ιMulti K 2 ![a, b] = z := by
  let e : (Fin 3 → K) ≃ₗ[K] V := (Module.finBasisOfFinrankEq K V hV).equivFun.symm
  obtain ⟨x, hx⟩ := exteriorPower.map_surjective (n := 2) e.surjective z
  have hx0 : x ≠ 0 := by
    intro h
    apply hz
    rw [← hx, h, map_zero]
  obtain ⟨a, b, hab, habx⟩ := exists_independent_pair_of_ne_zero hx0
  refine ⟨e a, e b, ?_, ?_⟩
  · convert hab.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective) using 1
    ext i
    fin_cases i <;> rfl
  · have hmap := congrArg (exteriorPower.map 2 e.toLinearMap) habx
    rw [exteriorPower.map_apply_ιMulti, hx] at hmap
    convert hmap using 1
    congr 1
    ext i
    fin_cases i <;> rfl

variable {W : Type w} [AddCommGroup W] [Module K W]

/-- In dimension three, nonvanishing on independent pairs proves the
actual linear map on the entire second exterior power is injective. -/
theorem injective_of_independent_wedges_ne_zero (hV : Module.finrank K V = 3)
    (L : (⋀[K]^2 V) →ₗ[K] W)
    (hL : ∀ a b : V, LinearIndependent K ![a, b] →
      L (exteriorPower.ιMulti K 2 ![a, b]) ≠ 0) : Function.Injective L := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro z hz
  change z = 0
  by_contra hz0
  obtain ⟨a, b, hab, habz⟩ := exists_independent_pair_of_finrank_three hV hz0
  apply hL a b hab
  rw [habz]
  exact hz

/-- Consequently an actual target receiving all independent wedges
nontrivially has dimension at least three. -/
theorem three_le_finrank_of_independent_wedges_ne_zero [FiniteDimensional K W]
    (hV : Module.finrank K V = 3) (L : (⋀[K]^2 V) →ₗ[K] W)
    (hL : ∀ a b : V, LinearIndependent K ![a, b] →
      L (exteriorPower.ιMulti K 2 ![a, b]) ≠ 0) : 3 ≤ Module.finrank K W := by
  have h := L.finrank_le_finrank_of_injective
    (injective_of_independent_wedges_ne_zero hV L hL)
  simpa [exteriorPower.finrank_eq, hV] using h

end GeneralSpace

end M9Native.MukaiThreeDimensionalBivectors
