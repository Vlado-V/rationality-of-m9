module

public import M9StacksIntegration.MukaiCastelnuovoLinear
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Literal ordered Plücker coordinates and exterior evaluation in dimension five

The native Grassmannian uses all twenty embeddings `Fin 2 ↪ Fin 5` as
coordinates. The linear map here keeps the ten increasing embeddings and
sends them to the corresponding actual exterior basis vectors. On the
literal maximal-minor tuple of a two-row matrix this map is the actual
wedge of its rows. No compression of the native Plücker scheme or
division by two is required.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

universe u v

namespace M9Native.MukaiOrderedMinors

variable {K : Type u} [Field K]

abbrev OrderedPair := Fin 2 ↪ Fin 5

def firstIndex : Fin 10 → Fin 5 := ![0,0,0,0,1,1,1,2,2,3]
def secondIndex : Fin 10 → Fin 5 := ![1,2,3,4,2,3,4,3,4,4]

theorem firstIndex_lt_secondIndex (p : Fin 10) : firstIndex p < secondIndex p := by
  fin_cases p <;> decide

/-- Each of the ten selected increasing embeddings is a genuine native
ordered Plücker index. -/
def pairEmbedding (p : Fin 10) : OrderedPair where
  toFun := ![firstIndex p,secondIndex p]
  inj' := by
    intro i j h
    have hij := (firstIndex_lt_secondIndex p).ne
    fin_cases i <;> fin_cases j <;> simp_all

@[simp] theorem pairEmbedding_zero (p : Fin 10) : pairEmbedding p 0 = firstIndex p := rfl
@[simp] theorem pairEmbedding_one (p : Fin 10) : pairEmbedding p 1 = secondIndex p := rfl

/-- The literal twenty minors of a two-row matrix, in the native index. -/
def orderedMinorCoordinates (a b : Fin 5 → K) : OrderedPair → K :=
  fun i => a (i 0) * b (i 1) - a (i 1) * b (i 0)

theorem orderedMinorCoordinates_eq_det (M : Matrix (Fin 2) (Fin 5) K)
    (i : OrderedPair) :
    orderedMinorCoordinates (M 0) (M 1) i = (M.submatrix id i).det := by
  simp [orderedMinorCoordinates,Matrix.det_fin_two]

/-- Select only increasing coordinates; the remaining native ordered
coordinates are legitimate ambient kernel directions. -/
def selectIncreasing : (OrderedPair → K) →ₗ[K] (Fin 10 → K) :=
  LinearMap.pi (fun p => LinearMap.proj (pairEmbedding p))

variable {W : Type v} [AddCommGroup W] [Module K W]

/-- Extend an actual alternating evaluation linearly from the twenty
ordered native coordinates, retaining just increasing basis wedges. -/
def orderedMinorMap (B : (Fin 5 → K) [⋀^Fin 2]→ₗ[K] W) :
    (OrderedPair → K) →ₗ[K] W :=
  (Fintype.linearCombination K (fun p : Fin 10 =>
    B ![Pi.single (firstIndex p) 1,Pi.single (secondIndex p) 1])).comp selectIncreasing

theorem orderedMinorMap_minors (B : (Fin 5 → K) [⋀^Fin 2]→ₗ[K] W)
    (a b : Fin 5 → K) :
    orderedMinorMap B (orderedMinorCoordinates a b) = B ![a,b] := by
  let e : Fin 5 → (Fin 5 → K) := fun i => Pi.single i 1
  have ha : a = ∑ i : Fin 5, a i • e i := by
    ext j
    simp [e,Pi.single_apply]
  have hb : b = ∑ i : Fin 5, b i • e i := by
    ext j
    simp [e,Pi.single_apply]
  have hd (i : Fin 5) : B ![e i,e i] = 0 :=
    MukaiCastelnuovoLinear.alternating_pair_diag B _
  have hs (i j : Fin 5) : B ![e j,e i] = -B ![e i,e j] :=
    MukaiCastelnuovoLinear.alternating_pair_swap B _ _
  calc
    orderedMinorMap B (orderedMinorCoordinates a b) =
        ∑ i : Fin 5, ∑ j : Fin 5, (a i * b j) • B ![e i,e j] := by
      simp only [orderedMinorMap,LinearMap.comp_apply,Fintype.linearCombination_apply,
        selectIncreasing,LinearMap.pi_apply,LinearMap.proj_apply,
        orderedMinorCoordinates,pairEmbedding_zero,pairEmbedding_one]
      norm_num [Fin.sum_univ_succ,firstIndex,secondIndex]
      rw [hd 0,hd 1,hd 2,hd 3,hd 4,
        hs 0 1,hs 0 2,hs 0 3,hs 0 4,hs 1 2,hs 1 3,hs 1 4,hs 2 3,hs 2 4,hs 3 4]
      simp [e]
      module
    _ = MukaiCastelnuovoLinear.asBilinear B a b := by
      conv_rhs => rw [ha,hb]
      simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,
        Finset.smul_sum,smul_smul,MukaiCastelnuovoLinear.asBilinear_apply]
      rw [Finset.sum_comm]
      simp only [mul_comm]
    _ = B ![a,b] := rfl

/-- The actual map from the twenty native coordinates to the genuine
second exterior power. -/
def orderedExteriorMap : (OrderedPair → K) →ₗ[K] (⋀[K]^2 (Fin 5 → K)) :=
  orderedMinorMap (exteriorPower.ιMulti K 2)

theorem orderedExteriorMap_minors (a b : Fin 5 → K) :
    orderedExteriorMap (orderedMinorCoordinates a b) = exteriorPower.ιMulti K 2 ![a,b] :=
  orderedMinorMap_minors _ a b

/-- A nonzero actual ordered-minor tuple means that the original two
rows are independent. -/
theorem linearIndependent_of_orderedMinors_ne_zero {a b : Fin 5 → K}
    (h : orderedMinorCoordinates a b ≠ 0) : LinearIndependent K ![a,b] := by
  rw [linearIndependent_fin2]
  constructor
  · intro hb
    change b = 0 at hb
    apply h
    ext i
    simp [orderedMinorCoordinates,hb]
  · intro t ht
    change t • b = a at ht
    apply h
    ext i
    simp [orderedMinorCoordinates,← ht,Pi.smul_apply]
    ring

end M9Native.MukaiOrderedMinors
