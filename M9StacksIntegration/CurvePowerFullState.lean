module

public import M9StacksIntegration.CurvePowerPairingReindex
public import M9StacksIntegration.CurvePowerGraphContextStepTransport

/-! The singleton-block partition realizes the original whole curve power.
The actual coordinate reindexing is retained, including the list-length
transport, before passing to genuine Chow-cap word degrees. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Stacks.CurvePower

universe u
namespace M9Native.CurvePowerFullState

open CurvePowerGraphLocal CurvePowerGraphMaps CurvePowerGraphMapReindex
open CurvePowerGraphDisjoint

def fullState (n : ℕ) : State := List.ofFn (fun i : Fin n => bit i.val)

@[simp] theorem fullState_length (n : ℕ) : (fullState n).length = n :=
  List.length_ofFn

@[simp] theorem fullState_get (n : ℕ) (j : Fin (fullState n).length) :
    (fullState n).get j = bit j.val := by
  simp [fullState]

theorem mem_fullState {n : ℕ} (i : Fin n) : bit i.val ∈ fullState n := by
  change bit i.val ∈ List.ofFn (fun j : Fin n => bit j.val)
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

theorem fullState_nonzero (n : ℕ) : ∀ a ∈ fullState n, a ≠ 0 := by
  intro a ha
  change a ∈ List.ofFn (fun j : Fin n => bit j.val) at ha
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
  exact Nat.ne_of_gt (Nat.two_pow_pos j.val)

theorem fullState_pairwise (n : ℕ) : (fullState n).Pairwise MaskDisjoint := by
  apply List.pairwise_ofFn.mpr
  intro i j hij
  apply (maskDisjoint_iff _ _).mpr
  intro v hi hj
  have hi' : i.val = v := by simpa only [bit, Nat.testBit_two_pow, decide_eq_true_eq] using hi
  have hj' : j.val = v := by simpa only [bit, Nat.testBit_two_pow, decide_eq_true_eq] using hj
  exact (ne_of_lt hij) (Fin.ext (hi'.trans hj'.symm))

theorem fullState_nodup (n : ℕ) : (fullState n).Nodup :=
  nodup_of_pairwise_nonzero _ (fullState_pairwise n) (fullState_nonzero n)

theorem fullState_separated (n : ℕ) : Separated (fullState n) :=
  separated_of_pairwise _ (fullState_pairwise n)

def indexEquiv (n : ℕ) : Fin n ≃ Fin (fullState n).length :=
  (finCongr (fullState_length n)).symm

@[simp] theorem indexEquiv_val (n : ℕ) (j : Fin n) :
    (indexEquiv n j).val = j.val := rfl

theorem blockAt_fullState {n : ℕ} (i : Fin n) :
    blockAt i.val (fullState n) = bit i.val :=
  CurvePowerGraphContextStepTransport.blockAt_eq_of_pairwise i.val (fullState n)
    (fullState_pairwise n) (bit i.val) (mem_fullState i) Nat.testBit_two_pow_self

theorem pointStep_fullState {n : ℕ} (i : Fin n) :
    pointStep i.val (fullState n) = some ((fullState n).erase (bit i.val)) := by
  simp only [pointStep, blockAt_fullState, bit,
    ite_eq_right (Nat.ne_of_gt (Nat.two_pow_pos i.val))]

variable {S : Scheme.{u}} (C : Over S) (c₀ : power C 0 ⟶ C)

/-- The singleton-block map is the actual finite-product reindexing,
with the original source-list length and the same coefficient base. -/
theorem stateMap_fullState_reindex (n : ℕ) :
    stateMap C c₀ n (fullState n) = reindex C (indexEquiv n) := by
  apply hom_ext n
  intro j
  rw [stateMap_coord, reindex_coord]
  apply stateCoordinate_eq_coord_of_unique C c₀ (fullState n)
    (fullState_separated n) j.val (indexEquiv n j)
  rw [fullState_get, indexEquiv_val]
  exact Nat.testBit_two_pow_self

end M9Native.CurvePowerFullState

namespace M9Native.CurvePowerFullState

open CurvePowerGraphLocal CurvePowerGraphMaps CurvePowerChowFunctional

variable (k : Type u) [Field k] (C : Over (Spec (.of k))) [IsProper C.hom]
  (c₀ : power C 0 ⟶ C)

/-- The actual partition functional on singleton blocks is the actual
intersection functional on the whole original curve power. -/
theorem partitionFunctional_fullState (n : ℕ) (word : List (LineClass C n)) :
    partitionFunctional k C c₀ n word (fullState n) =
      wordDegree k (power C n).hom (word.map chosenLine) := by
  unfold partitionFunctional
  rw [stateMap_fullState_reindex]
  simpa only [List.map_map, Function.comp_def] using
    CurvePowerPairingReindex.wordDegree_reindex k C (indexEquiv n) word

theorem tautologicalFunctional_fullState [SmoothOfRelativeDimension 1 C.hom]
    (n : ℕ) (word : List (Letter n)) :
    tautologicalFunctional k C c₀ n word (fullState n) =
      CurvePowerPointTrace.actualWordDegree k C c₀ n word :=
  partitionFunctional_fullState k C c₀ n (word.map (letterClass k C c₀ n))

end M9Native.CurvePowerFullState
