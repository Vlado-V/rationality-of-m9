module

public import M9.PrimitiveRepresentation
public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
public import Mathlib.Tactic

/-!
# The actual primitive third exterior power

The carrier is Mathlib's `⋀[K]^3 (Fin 6 → K)`. Contraction is descended from
the displayed alternating trilinear map in Section 2.1 of the manuscript.
Its actual kernel is explicitly identified with the fourteen-coordinate matrix
model. The actual exterior wedge and ordered volume induce exactly the stated
trace-difference pairing, including Gram weight two on off-diagonal symmetric
vectors. No exterior space or kernel is introduced by an unrelated coordinate definition.
-/

@[expose] public section
noncomputable section

namespace M9.ExteriorPrimitive

open Module Matrix exteriorPower
open scoped BigOperators

variable (K : Type*) [Field K]

abbrev V := Fin 6 → K
abbrev Third := ⋀[K]^3 (V K)

def eIndex (i : Fin 3) : Fin 6 := i.castAdd 3
def fIndex (i : Fin 3) : Fin 6 := Fin.natAdd 3 i

def basisVector (i : Fin 6) : V K := Pi.single i 1
def e (i : Fin 3) : V K := basisVector K (eIndex i)
def f (i : Fin 3) : V K := basisVector K (fIndex i)

/-- The paper's sign convention, `ω(e_i,f_j)=δ_ij`. -/
def omegaValue (u v : V K) : K :=
  ∑ i : Fin 3, (u (eIndex i) * v (fIndex i) - u (fIndex i) * v (eIndex i))

def omega : LinearMap.BilinForm K (V K) :=
  LinearMap.mk₂ K (omegaValue K)
    (by intro u v w; simp [omegaValue, Fin.sum_univ_succ]; ring)
    (by intro c u v; simp [omegaValue, Fin.sum_univ_succ]; ring)
    (by intro u v w; simp [omegaValue, Fin.sum_univ_succ]; ring)
    (by intro c u v; simp [omegaValue, Fin.sum_univ_succ]; ring)

@[simp] theorem omega_apply (u v : V K) : omega K u v = omegaValue K u v := rfl

@[simp] theorem omegaValue_self (u : V K) : omegaValue K u u = 0 := by
  simp [omegaValue, mul_comm]

@[simp] theorem omega_self (u : V K) : omega K u u = 0 := by
  exact omegaValue_self K u

theorem omega_swap (u v : V K) : omega K u v = -omega K v u := by
  simp only [omega_apply, omegaValue, Fin.sum_univ_succ]
  ring

def tripleContract (u v w : V K) : V K :=
  omega K u v • w - omega K u w • v + omega K v w • u

/-- The actual contraction formula before descent to the exterior power. -/
def contractionFormula (v : Fin 3 → V K) : V K := tripleContract K (v 0) (v 1) (v 2)

theorem tripleContract_add_left (x y v w : V K) :
    tripleContract K (x+y) v w = tripleContract K x v w + tripleContract K y v w := by
  funext k
  simp [tripleContract, omegaValue, Fin.sum_univ_succ, smul_eq_mul]
  ring

theorem tripleContract_add_middle (u x y w : V K) :
    tripleContract K u (x+y) w = tripleContract K u x w + tripleContract K u y w := by
  funext k
  simp [tripleContract, omegaValue, Fin.sum_univ_succ, smul_eq_mul]
  ring

theorem tripleContract_add_right (u v x y : V K) :
    tripleContract K u v (x+y) = tripleContract K u v x + tripleContract K u v y := by
  funext k
  simp [tripleContract, omegaValue, Fin.sum_univ_succ, smul_eq_mul]
  ring

theorem tripleContract_smul_left (c : K) (u v w : V K) :
    tripleContract K (c • u) v w = c • tripleContract K u v w := by
  funext k
  simp [tripleContract, omegaValue, Fin.sum_univ_succ, smul_eq_mul]
  ring

theorem tripleContract_smul_middle (c : K) (u v w : V K) :
    tripleContract K u (c • v) w = c • tripleContract K u v w := by
  funext k
  simp [tripleContract, omegaValue, Fin.sum_univ_succ, smul_eq_mul]
  ring

theorem tripleContract_smul_right (c : K) (u v w : V K) :
    tripleContract K u v (c • w) = c • tripleContract K u v w := by
  funext k
  simp [tripleContract, omegaValue, Fin.sum_univ_succ, smul_eq_mul]
  ring

def contractionAlternating : (V K) [⋀^Fin 3]→ₗ[K] V K where
  toMultilinearMap := MultilinearMap.mk' (contractionFormula K)
    (by
      intro v i x y
      fin_cases i
      · change tripleContract K (x+y) (v 1) (v 2) = tripleContract K x (v 1) (v 2) + tripleContract K y (v 1) (v 2)
        exact tripleContract_add_left K x y _ _
      · change tripleContract K (v 0) (x+y) (v 2) = tripleContract K (v 0) x (v 2) + tripleContract K (v 0) y (v 2)
        exact tripleContract_add_middle K _ x y _
      · change tripleContract K (v 0) (v 1) (x+y) = tripleContract K (v 0) (v 1) x + tripleContract K (v 0) (v 1) y
        exact tripleContract_add_right K _ _ x y)
    (by
      intro v i c x
      fin_cases i
      · change tripleContract K (c • x) (v 1) (v 2) = c • tripleContract K x (v 1) (v 2)
        exact tripleContract_smul_left K c x _ _
      · change tripleContract K (v 0) (c • x) (v 2) = c • tripleContract K (v 0) x (v 2)
        exact tripleContract_smul_middle K c _ x _
      · change tripleContract K (v 0) (v 1) (c • x) = c • tripleContract K (v 0) (v 1) x
        exact tripleContract_smul_right K c _ _ x)
  map_eq_zero_of_eq' v i j hij hne := by
    change contractionFormula K v = 0
    have hv : v 0 = v 1 ∨ v 0 = v 2 ∨ v 1 = v 2 := by
      fin_cases i <;> fin_cases j <;> simp_all
    rcases hv with hv | hv | hv
    · simp [contractionFormula, tripleContract, hv]
    · funext k
      simp only [contractionFormula, tripleContract, hv, omega_self, Pi.add_apply, Pi.smul_apply,
        zero_smul, sub_zero, smul_eq_mul, Pi.zero_apply]
      rw [omega_swap K (v 2) (v 1)]
      ring
    · simp [contractionFormula, tripleContract, hv]

/-- Contraction on Mathlib's actual third exterior power. -/
def contraction : Third K →ₗ[K] V K :=
  exteriorPower.alternatingMapLinearEquiv (contractionAlternating K)

@[simp] theorem contraction_ιMulti (v : Fin 3 → V K) :
    contraction K (exteriorPower.ιMulti K 3 v) = contractionFormula K v :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

def wedge3 (u v w : V K) : Third K := exteriorPower.ιMulti K 3 ![u,v,w]

@[simp] theorem contraction_wedge3 (u v w : V K) :
    contraction K (wedge3 K u v w) = omega K u v • w - omega K u w • v + omega K v w • u := by
  simp [wedge3, contractionFormula, tripleContract]

/-- The actual primitive submodule, rather than a coordinate surrogate. -/
def Primitive : Submodule K (Third K) := LinearMap.ker (contraction K)

@[simp] theorem finrank_third : finrank K (Third K) = 20 := by
  rw [Third, exteriorPower.finrank_eq]
  norm_num [V, Module.finrank_pi, Nat.choose]

@[simp] theorem omega_e_e (i j : Fin 3) : omega K (e K i) (e K j) = 0 := by
  change omegaValue K (e K i) (e K j) = 0
  fin_cases i <;> fin_cases j <;>
    simp only [omegaValue, Fin.sum_univ_succ, e, basisVector, eIndex, fIndex] <;>
    norm_num [Pi.single_apply]

@[simp] theorem omega_f_f (i j : Fin 3) : omega K (f K i) (f K j) = 0 := by
  change omegaValue K (f K i) (f K j) = 0
  fin_cases i <;> fin_cases j <;>
    simp only [omegaValue, Fin.sum_univ_succ, f, basisVector, eIndex, fIndex] <;>
    norm_num [Pi.single_apply]

@[simp] theorem omega_e_f (i j : Fin 3) : omega K (e K i) (f K j) = if i=j then 1 else 0 := by
  change omegaValue K (e K i) (f K j) = if i=j then 1 else 0
  fin_cases i <;> fin_cases j <;>
    simp only [omegaValue, Fin.sum_univ_succ, e, f, basisVector, eIndex, fIndex] <;>
    norm_num [Pi.single_apply]

@[simp] theorem omega_f_e (i j : Fin 3) : omega K (f K i) (e K j) = if i=j then -1 else 0 := by
  rw [omega_swap, omega_e_f]
  split_ifs <;> simp_all

/-- Six actual decomposable preimages prove that contraction is onto. -/
def contractionSectionBasis : Fin 6 → Third K :=
  ![wedge3 K (e K 0) (e K 1) (f K 1), wedge3 K (e K 1) (e K 2) (f K 2),
    wedge3 K (e K 2) (e K 0) (f K 0), wedge3 K (e K 1) (f K 1) (f K 0),
    wedge3 K (e K 2) (f K 2) (f K 1), wedge3 K (e K 0) (f K 0) (f K 2)]

@[simp] theorem contractionSectionBasis_apply (i : Fin 6) :
    contraction K (contractionSectionBasis K i) = basisVector K i := by
  fin_cases i <;> simp [contractionSectionBasis, e, f, eIndex, fIndex, basisVector,
    omegaValue, Fin.sum_univ_succ]

theorem contraction_surjective : Function.Surjective (contraction K) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← (Pi.basisFun K (Fin 6)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  refine ⟨contractionSectionBasis K i, ?_⟩
  simpa only [basisVector, Pi.basisFun_apply] using contractionSectionBasis_apply K i

@[simp] theorem finrank_primitive : finrank K (Primitive K) = 14 := by
  have h := (contraction K).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (contraction_surjective K), finrank_top, finrank_third] at h
  have hV : finrank K (V K) = 6 := by simp [V]
  rw [hV] at h
  change finrank K (LinearMap.ker (contraction K)) = 14
  omega

def nextOne : Fin 3 → Fin 3 := ![1,2,0]
def nextTwo : Fin 3 → Fin 3 := ![2,0,1]

def a : Third K := wedge3 K (e K 0) (e K 1) (e K 2)
def b : Third K := wedge3 K (f K 0) (f K 1) (f K 2)

/-- The paper's `q_ij=e_i∧ι_phi_j(b)`, using the cyclic cofactor orientation. -/
def q (i j : Fin 3) : Third K := wedge3 K (e K i) (f K (nextOne j)) (f K (nextTwo j))

/-- The paper's `p_ij=f_i∧ι_epsilon_j(a)`, with the same orientation. -/
def p (i j : Fin 3) : Third K := wedge3 K (f K i) (e K (nextOne j)) (e K (nextTwo j))

/-- A genuine exterior-coordinate functional, obtained by exterior duality. -/
def coordinate (i j k : Fin 6) : Third K →ₗ[K] K :=
  exteriorPower.pairingDual K (V K) 3
    (exteriorPower.ιMulti K 3 ![LinearMap.proj i, LinearMap.proj j, LinearMap.proj k])

@[simp] theorem coordinate_wedge3 (i j k : Fin 6) (u v w : V K) :
    coordinate K i j k (wedge3 K u v w) =
      u i * v j * w k + u j * v k * w i + u k * v i * w j -
        u i * v k * w j - u j * v i * w k - u k * v j * w i := by
  simp [coordinate, wedge3, Matrix.det_fin_three]
  ring

def aCoordinate : Third K →ₗ[K] K := coordinate K 0 1 2
def bCoordinate : Third K →ₗ[K] K := coordinate K 3 4 5
def qCoordinate (i j : Fin 3) : Third K →ₗ[K] K :=
  coordinate K (eIndex i) (fIndex (nextOne j)) (fIndex (nextTwo j))
def pCoordinate (i j : Fin 3) : Third K →ₗ[K] K :=
  coordinate K (fIndex i) (eIndex (nextOne j)) (eIndex (nextTwo j))

private theorem exteriorIndex_disjoint (i j : Fin 3) : eIndex i ≠ fIndex j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [eIndex, fIndex, Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

private theorem exteriorBasis_e_e (i j : Fin 3) :
    e K j (eIndex i) = if i = j then 1 else 0 := by
  simp [e, eIndex, basisVector, Pi.single_apply, Fin.ext_iff]

private theorem exteriorBasis_f_f (i j : Fin 3) :
    f K j (fIndex i) = if i = j then 1 else 0 := by
  simp [f, fIndex, basisVector, Pi.single_apply, Fin.ext_iff]

private theorem exteriorBasis_e_f (i j : Fin 3) : e K j (fIndex i) = 0 := by
  simp [e, basisVector, (exteriorIndex_disjoint j i).symm]

private theorem exteriorBasis_f_e (i j : Fin 3) : f K j (eIndex i) = 0 := by
  simp [f, basisVector, exteriorIndex_disjoint i j]

/-- The cyclic two-coordinate minor is the Kronecker delta for its omitted index. -/
private theorem exteriorCofactorMinor (j l : Fin 3) :
    (if nextOne j = nextOne l then (1 : K) else 0) *
      (if nextTwo j = nextTwo l then 1 else 0) -
    (if nextTwo j = nextOne l then 1 else 0) *
      (if nextOne j = nextTwo l then 1 else 0) =
    (if j = l then 1 else 0) := by
  fin_cases j <;> fin_cases l <;> norm_num [nextOne, nextTwo]

@[simp] theorem qCoordinate_q (i j k l : Fin 3) :
    qCoordinate K i j (q K k l) = if i=k then if j=l then 1 else 0 else 0 := by
  simp only [qCoordinate, q, coordinate_wedge3, exteriorBasis_e_e, exteriorBasis_f_f,
    exteriorBasis_e_f, exteriorBasis_f_e, zero_mul, mul_zero, add_zero, sub_zero,
    mul_assoc, ← mul_sub, exteriorCofactorMinor]
  split <;> simp_all

@[simp] theorem qCoordinate_p (i j k l : Fin 3) : qCoordinate K i j (p K k l) = 0 := by
  simp only [qCoordinate, p, coordinate_wedge3, exteriorBasis_e_f, exteriorBasis_f_e,
    zero_mul, mul_zero, add_zero, sub_zero]

@[simp] theorem pCoordinate_p (i j k l : Fin 3) :
    pCoordinate K i j (p K k l) = if i=k then if j=l then 1 else 0 else 0 := by
  simp only [pCoordinate, p, coordinate_wedge3, exteriorBasis_e_e, exteriorBasis_f_f,
    exteriorBasis_e_f, exteriorBasis_f_e, zero_mul, mul_zero, add_zero, sub_zero,
    mul_assoc, ← mul_sub, exteriorCofactorMinor]
  split <;> simp_all

@[simp] theorem pCoordinate_q (i j k l : Fin 3) : pCoordinate K i j (q K k l) = 0 := by
  simp only [pCoordinate, q, coordinate_wedge3, exteriorBasis_e_f, exteriorBasis_f_e,
    zero_mul, mul_zero, add_zero, sub_zero]


@[simp] theorem aCoordinate_a : aCoordinate K (a K) = 1 := by
  norm_num [aCoordinate, a, e, eIndex, basisVector]
@[simp] theorem aCoordinate_b : aCoordinate K (b K) = 0 := by
  norm_num [aCoordinate, b, f, fIndex, basisVector]
@[simp] theorem bCoordinate_a : bCoordinate K (a K) = 0 := by
  norm_num [bCoordinate, a, e, eIndex, basisVector]
@[simp] theorem bCoordinate_b : bCoordinate K (b K) = 1 := by
  norm_num [bCoordinate, b, f, fIndex, basisVector]

@[simp] theorem aCoordinate_q (i j : Fin 3) : aCoordinate K (q K i j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [aCoordinate, q, e, f, nextOne, nextTwo, eIndex, fIndex, basisVector]
@[simp] theorem aCoordinate_p (i j : Fin 3) : aCoordinate K (p K i j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [aCoordinate, p, e, f, nextOne, nextTwo, eIndex, fIndex, basisVector]
@[simp] theorem bCoordinate_q (i j : Fin 3) : bCoordinate K (q K i j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [bCoordinate, q, e, f, nextOne, nextTwo, eIndex, fIndex, basisVector]
@[simp] theorem bCoordinate_p (i j : Fin 3) : bCoordinate K (p K i j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [bCoordinate, p, e, f, nextOne, nextTwo, eIndex, fIndex, basisVector]
@[simp] theorem qCoordinate_a (i j : Fin 3) : qCoordinate K i j (a K) = 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [qCoordinate, a, e, f, nextOne, nextTwo, eIndex, fIndex, basisVector]
@[simp] theorem qCoordinate_b (i j : Fin 3) : qCoordinate K i j (b K) = 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [qCoordinate, b, e, f, nextOne, nextTwo, eIndex, fIndex, basisVector]
@[simp] theorem pCoordinate_a (i j : Fin 3) : pCoordinate K i j (a K) = 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [pCoordinate, a, e, f, nextOne, nextTwo, eIndex, fIndex, basisVector]
@[simp] theorem pCoordinate_b (i j : Fin 3) : pCoordinate K i j (b K) = 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [pCoordinate, b, e, f, nextOne, nextTwo, eIndex, fIndex, basisVector]

/-- Sum of the actual mixed wedges with their full matrix coefficients. -/
def mixedQ : Matrix (Fin 3) (Fin 3) K →ₗ[K] Third K where
  toFun X := ∑ i, ∑ j, X i j • q K i j
  map_add' X Y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c X := by simp [Finset.smul_sum, smul_smul]

def mixedP : Matrix (Fin 3) (Fin 3) K →ₗ[K] Third K where
  toFun X := ∑ i, ∑ j, X i j • p K i j
  map_add' X Y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c X := by simp [Finset.smul_sum, smul_smul]

/-- The manuscript's literal expansion in the actual exterior power. -/
def coordinateEmbedding : PrimitiveRepresentation.Coordinates K →ₗ[K] Third K where
  toFun r := r.1 • a K + mixedQ K r.2.1.val + mixedP K r.2.2.1.val + r.2.2.2 • b K
  map_add' r s := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add, add_smul]
    module
  map_smul' c r := by
    change (c * r.1) • a K + mixedQ K (c • r.2.1.val) +
      mixedP K (c • r.2.2.1.val) + (c * r.2.2.2) • b K =
      c • (r.1 • a K + mixedQ K r.2.1.val + mixedP K r.2.2.1.val + r.2.2.2 • b K)
    simp [smul_add, smul_smul]

@[simp] theorem aCoordinate_embedding (r : PrimitiveRepresentation.Coordinates K) :
    aCoordinate K (coordinateEmbedding K r) = r.1 := by
  simp [coordinateEmbedding, mixedQ, mixedP]
@[simp] theorem bCoordinate_embedding (r : PrimitiveRepresentation.Coordinates K) :
    bCoordinate K (coordinateEmbedding K r) = r.2.2.2 := by
  simp [coordinateEmbedding, mixedQ, mixedP]
@[simp] theorem qCoordinate_embedding (r : PrimitiveRepresentation.Coordinates K) (i j : Fin 3) :
    qCoordinate K i j (coordinateEmbedding K r) = r.2.1.val i j := by
  classical
  simp [coordinateEmbedding, mixedQ, mixedP, smul_eq_mul, mul_ite]
@[simp] theorem pCoordinate_embedding (r : PrimitiveRepresentation.Coordinates K) (i j : Fin 3) :
    pCoordinate K i j (coordinateEmbedding K r) = r.2.2.1.val i j := by
  classical
  simp [coordinateEmbedding, mixedQ, mixedP, smul_eq_mul, mul_ite]

/-- Extract upper-triangular exterior coefficients and reconstruct a symmetric matrix. -/
def qExtraction : Third K →ₗ[K] Symmetric3 K :=
  (symmetric3Coordinates K).symm.toLinearMap.comp
    (LinearMap.pi fun ij : Upper3 => qCoordinate K ij.val.1 ij.val.2)
def pExtraction : Third K →ₗ[K] Symmetric3 K :=
  (symmetric3Coordinates K).symm.toLinearMap.comp
    (LinearMap.pi fun ij : Upper3 => pCoordinate K ij.val.1 ij.val.2)

/-- Explicit coordinate extraction on the entire actual third exterior power. -/
def coordinateProjection : Third K →ₗ[K] PrimitiveRepresentation.Coordinates K :=
  (aCoordinate K).prod ((qExtraction K).prod ((pExtraction K).prod (bCoordinate K)))

@[simp] theorem qExtraction_embedding (r : PrimitiveRepresentation.Coordinates K) :
    qExtraction K (coordinateEmbedding K r) = r.2.1 := by
  change (symmetric3Coordinates K).symm
    ((LinearMap.pi fun ij : Upper3 => qCoordinate K ij.val.1 ij.val.2)
      (coordinateEmbedding K r)) = r.2.1
  apply (symmetric3Coordinates K).injective
  rw [LinearEquiv.apply_symm_apply]
  funext ij
  exact qCoordinate_embedding K r ij.val.1 ij.val.2
@[simp] theorem pExtraction_embedding (r : PrimitiveRepresentation.Coordinates K) :
    pExtraction K (coordinateEmbedding K r) = r.2.2.1 := by
  change (symmetric3Coordinates K).symm
    ((LinearMap.pi fun ij : Upper3 => pCoordinate K ij.val.1 ij.val.2)
      (coordinateEmbedding K r)) = r.2.2.1
  apply (symmetric3Coordinates K).injective
  rw [LinearEquiv.apply_symm_apply]
  funext ij
  exact pCoordinate_embedding K r ij.val.1 ij.val.2

@[simp] theorem coordinateProjection_embedding (r : PrimitiveRepresentation.Coordinates K) :
    coordinateProjection K (coordinateEmbedding K r) = r := by
  change (aCoordinate K (coordinateEmbedding K r), qExtraction K (coordinateEmbedding K r),
    pExtraction K (coordinateEmbedding K r), bCoordinate K (coordinateEmbedding K r)) = r
  simp only [aCoordinate_embedding, bCoordinate_embedding, qExtraction_embedding, pExtraction_embedding]

theorem coordinateEmbedding_injective : Function.Injective (coordinateEmbedding K) :=
  Function.LeftInverse.injective (coordinateProjection_embedding K)

@[simp] theorem contraction_a : contraction K (a K) = 0 := by
  simp [a, -omega_apply]
@[simp] theorem contraction_b : contraction K (b K) = 0 := by
  simp [b, -omega_apply]

theorem contraction_q_swap (i j : Fin 3) :
    contraction K (q K j i) = -contraction K (q K i j) := by
  fin_cases i <;> fin_cases j <;> simp [q, nextOne, nextTwo, -omega_apply]
theorem contraction_p_swap (i j : Fin 3) :
    contraction K (p K j i) = -contraction K (p K i j) := by
  fin_cases i <;> fin_cases j <;> simp [p, nextOne, nextTwo, -omega_apply]

/-- Symmetric coefficients annihilate a skew family in characteristic zero. -/
theorem sum_symmetric_skew_zero [CharZero K] {M : Type*} [AddCommGroup M] [Module K M]
    (X : Symmetric3 K) (z : Fin 3 → Fin 3 → M) (hz : ∀ i j, z j i = -z i j) :
    (∑ i, ∑ j, X.val i j • z i j) = 0 := by
  have hX (i j : Fin 3) : X.val j i = X.val i j := congrFun (congrFun X.property i) j
  have hneg : (∑ i, ∑ j, X.val i j • z i j) = -(∑ i, ∑ j, X.val i j • z i j) := by
    calc
      _ = ∑ j, ∑ i, X.val i j • z i j := Finset.sum_comm
      _ = ∑ j, ∑ i, -(X.val j i • z j i) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        rw [hX i j, hz j i, smul_neg]
      _ = _ := by simp
  have htwo : (2 : K) • (∑ i, ∑ j, X.val i j • z i j) = 0 := by
    rw [two_smul]
    nth_rw 1 [hneg]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp htwo).resolve_left two_ne_zero

@[simp] theorem contraction_mixedQ [CharZero K] (X : Symmetric3 K) :
    contraction K (mixedQ K X.val) = 0 := by
  simp only [mixedQ, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]
  exact sum_symmetric_skew_zero K X _ (contraction_q_swap K)
@[simp] theorem contraction_mixedP [CharZero K] (X : Symmetric3 K) :
    contraction K (mixedP K X.val) = 0 := by
  simp only [mixedP, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul]
  exact sum_symmetric_skew_zero K X _ (contraction_p_swap K)

@[simp] theorem contraction_embedding [CharZero K] (r : PrimitiveRepresentation.Coordinates K) :
    contraction K (coordinateEmbedding K r) = 0 := by
  simp [coordinateEmbedding]

/-- The coordinate expansion takes values in the actual kernel of contraction. -/
def embeddingIntoPrimitive [CharZero K] : PrimitiveRepresentation.Coordinates K →ₗ[K] Primitive K :=
  (coordinateEmbedding K).codRestrict (Primitive K) (by
    intro r
    exact contraction_embedding K r)

theorem embeddingIntoPrimitive_bijective [CharZero K] :
    Function.Bijective (embeddingIntoPrimitive K) := by
  have hinj : Function.Injective (embeddingIntoPrimitive K) := by
    intro r s h
    apply coordinateEmbedding_injective K
    exact congrArg Subtype.val h
  refine ⟨hinj, ?_⟩
  have hdim : finrank K (PrimitiveRepresentation.Coordinates K) = finrank K (Primitive K) := by
    rw [PrimitiveRepresentation.finrank_coordinates, finrank_primitive]
  exact LinearMap.range_eq_top.mp
    (Submodule.eq_top_of_finrank_eq (K := K) (V := Primitive K)
      (S := (embeddingIntoPrimitive K).range)
      ((LinearMap.finrank_range_of_inj (f := embeddingIntoPrimitive K) hinj).trans hdim))

/-- The explicit fourteen-coordinate model is the actual primitive exterior subspace. -/
def primitiveEquiv [CharZero K] : PrimitiveRepresentation.Coordinates K ≃ₗ[K] Primitive K :=
  LinearEquiv.ofBijective (embeddingIntoPrimitive K) (embeddingIntoPrimitive_bijective K)

@[simp] theorem primitiveEquiv_val [CharZero K] (r : PrimitiveRepresentation.Coordinates K) :
    (primitiveEquiv K r).val = coordinateEmbedding K r := rfl

@[simp] theorem primitiveEquiv_symm [CharZero K] (w : Primitive K) :
    (primitiveEquiv K).symm w = coordinateProjection K w.val := by
  obtain ⟨r, rfl⟩ := (primitiveEquiv K).surjective w
  simp


/-- Coefficient of `e₁∧e₂∧e₃∧f₁∧f₂∧f₃` in the actual top exterior power. -/
def volumeCoordinate : (⋀[K]^6 (V K)) →ₗ[K] K :=
  exteriorPower.pairingDual K (V K) 6
    (exteriorPower.ιMulti K 6 (fun i : Fin 6 => LinearMap.proj i))

/-- The actual exterior multiplication, evaluated against the ordered volume. -/
def ambientPairing : LinearMap.BilinForm K (Third K) :=
  (exteriorPower.wedge K (V K) 3 3).compr₂ (volumeCoordinate K)

theorem wedge_ιMulti (u v : Fin 3 → V K) :
    exteriorPower.wedge K (V K) 3 3 (exteriorPower.ιMulti K 3 u)
      (exteriorPower.ιMulti K 3 v) = exteriorPower.ιMulti K 6 (Fin.append u v) := by
  apply Subtype.ext
  simp only [exteriorPower.wedge, DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul,
    exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_mul_ιMulti]

@[simp] theorem ambientPairing_ιMulti (u v : Fin 3 → V K) :
    ambientPairing K (exteriorPower.ιMulti K 3 u) (exteriorPower.ιMulti K 3 v) =
      Matrix.det (Matrix.of fun i j : Fin 6 => Fin.append u v i j) := by
  change volumeCoordinate K (exteriorPower.wedge K (V K) 3 3
    (exteriorPower.ιMulti K 3 u) (exteriorPower.ιMulti K 3 v)) = _
  rw [wedge_ιMulti]
  simp [volumeCoordinate]


/- Scratch-only optimization helpers: exact original Gram identities,
using repeated rows or permutation determinants instead of Laplace trees. -/
private theorem pairing_zero_of_repeated_row (u v : Fin 3 → V K)
    (i j : Fin 6) (hne : i ≠ j)
    (hrow : Fin.append u v i = Fin.append u v j) :
    ambientPairing K (exteriorPower.ιMulti K 3 u) (exteriorPower.ιMulti K 3 v) = 0 := by
  rw [ambientPairing_ιMulti]
  exact Matrix.det_zero_of_row_eq hne hrow

private theorem cyclic_pairs_intersect (j l : Fin 3) :
    nextOne j = nextOne l ∨ nextOne j = nextTwo l ∨
      nextTwo j = nextOne l ∨ nextTwo j = nextTwo l := by
  fin_cases j <;> fin_cases l <;> decide

private theorem cyclic_cases (i j : Fin 3) :
    i = j ∨ i = nextOne j ∨ i = nextTwo j := by
  fin_cases i <;> fin_cases j <;> decide

private theorem left_basis_tuple : (![e K 0, e K 1, e K 2] : Fin 3 → V K) = e K := by
  funext i
  fin_cases i <;> rfl

private theorem right_basis_tuple : (![f K 0, f K 1, f K 2] : Fin 3 → V K) = f K := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem ambientPairing_a_b : ambientPairing K (a K) (b K) = 1 := by

  simp only [a, b, wedge3, ambientPairing_ιMulti]
  have hM : (Matrix.of fun i j : Fin 6 => Fin.append
      ![e K 0, e K 1, e K 2] ![f K 0, f K 1, f K 2] i j) =
        (1 : Matrix (Fin 6) (Fin 6) K) := by
    ext i j
    fin_cases i <;>
      simp [Fin.append, Fin.addCases, e, f, basisVector, eIndex, fIndex,
        Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [hM, Matrix.det_one]

/-- The ordered top wedge used in the manuscript. -/
def volume : ⋀[K]^6 (V K) := exteriorPower.wedge K (V K) 3 3 (a K) (b K)

@[simp] theorem volume_coe : (volume K : ExteriorAlgebra K (V K)) =
    (a K : ExteriorAlgebra K (V K)) * (b K : ExteriorAlgebra K (V K)) := rfl

@[simp] theorem volumeCoordinate_volume : volumeCoordinate K (volume K) = 1 :=
  ambientPairing_a_b K

/-- Trivialization of the actual top exterior power by the ordered volume. -/
def volumeEquiv : (⋀[K]^6 (V K)) ≃ₗ[K] K := by
  have hsurj : Function.Surjective (volumeCoordinate K) := by
    intro c
    refine ⟨c • volume K, ?_⟩
    simp
  have hdim : finrank K (⋀[K]^6 (V K)) = finrank K K := by
    rw [exteriorPower.finrank_eq]
    simp [V]
  exact LinearEquiv.ofBijective (volumeCoordinate K)
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := volumeCoordinate K) hdim).mpr hsurj, hsurj⟩

@[simp] theorem volumeEquiv_apply (x : ⋀[K]^6 (V K)) :
    volumeEquiv K x = volumeCoordinate K x := rfl

@[simp] theorem volumeEquiv_symm_apply (c : K) :
    (volumeEquiv K).symm c = c • volume K := by
  apply (volumeEquiv K).injective
  simp

theorem ambientPairing_neg_swap (x y : Third K) :
    ambientPairing K x y = -ambientPairing K y x := by
  have hmap : ambientPairing K = -(ambientPairing K).flip := by
    apply exteriorPower.linearMap_ext
    apply DFunLike.ext
    intro u
    apply exteriorPower.linearMap_ext
    apply DFunLike.ext
    intro v
    change volumeCoordinate K (exteriorPower.wedge K (V K) 3 3
      (exteriorPower.ιMulti K 3 u) (exteriorPower.ιMulti K 3 v)) =
      -volumeCoordinate K (exteriorPower.wedge K (V K) 3 3
      (exteriorPower.ιMulti K 3 v) (exteriorPower.ιMulti K 3 u))
    rw [← map_neg]
    apply congrArg (volumeCoordinate K)
    apply Subtype.ext
    change ExteriorAlgebra.ιMulti K 3 u * ExteriorAlgebra.ιMulti K 3 v =
      -(ExteriorAlgebra.ιMulti K 3 v * ExteriorAlgebra.ιMulti K 3 u)
    have hsign : ((-1 : ℤˣ) ^ (3 * 3)) = -1 := by decide
    simpa only [hsign, Units.neg_smul, one_smul] using
      (ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm K u v)
  exact congrArg (fun B : LinearMap.BilinForm K (Third K) => B x y) hmap

@[simp] theorem ambientPairing_b_a : ambientPairing K (b K) (a K) = -1 := by
  rw [ambientPairing_neg_swap, ambientPairing_a_b]


/-- Actual primitive vectors are determined by the stated exterior coefficients. -/
theorem primitive_ext_upper [CharZero K] (u v : Primitive K)
    (ha : aCoordinate K u.val = aCoordinate K v.val)
    (hb : bCoordinate K u.val = bCoordinate K v.val)
    (hq : ∀ ij : Upper3, qCoordinate K ij.val.1 ij.val.2 u.val =
      qCoordinate K ij.val.1 ij.val.2 v.val)
    (hp : ∀ ij : Upper3, pCoordinate K ij.val.1 ij.val.2 u.val =
      pCoordinate K ij.val.1 ij.val.2 v.val) : u = v := by
  have hq' : qExtraction K u.val = qExtraction K v.val := by
    apply (symmetric3Coordinates K).injective
    simp only [qExtraction, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply]
    funext ij
    exact hq ij
  have hp' : pExtraction K u.val = pExtraction K v.val := by
    apply (symmetric3Coordinates K).injective
    simp only [pExtraction, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply]
    funext ij
    exact hp ij
  apply (primitiveEquiv K).symm.injective
  rw [primitiveEquiv_symm, primitiveEquiv_symm]
  change (aCoordinate K u.val, qExtraction K u.val, pExtraction K u.val, bCoordinate K u.val) =
    (aCoordinate K v.val, qExtraction K v.val, pExtraction K v.val, bCoordinate K v.val)
  rw [ha, hb, hq', hp']

/-- The six symmetric-matrix basis vectors use the actual upper-triangular matrix model. -/
def symmetricBasis : Basis Upper3 K (Symmetric3 K) :=
  (Pi.basisFun K Upper3).map (symmetric3Coordinates K).symm

abbrev PrimitiveBasisIndex := Unit ⊕ (Upper3 ⊕ (Upper3 ⊕ Unit))

@[simp] theorem card_primitiveBasisIndex : Fintype.card PrimitiveBasisIndex = 14 := by simp [PrimitiveBasisIndex]

/-- The coordinate basis has the two scalar vectors and two six-element symmetric blocks. -/
def coordinateBasis : Basis PrimitiveBasisIndex K (PrimitiveRepresentation.Coordinates K) :=
  (Basis.singleton Unit K).prod ((symmetricBasis K).prod
    ((symmetricBasis K).prod (Basis.singleton Unit K)))

/-- A genuine fourteen-element basis of the actual kernel of contraction. -/
def primitiveBasis [CharZero K] : Basis PrimitiveBasisIndex K (Primitive K) :=
  (coordinateBasis K).map (primitiveEquiv K)

@[simp] theorem primitiveBasis_val [CharZero K] (i : PrimitiveBasisIndex) :
    (primitiveBasis K i).val = coordinateEmbedding K (coordinateBasis K i) := by
  simp [primitiveBasis]

@[simp] theorem ambientPairing_a_a : ambientPairing K (a K) (a K) = 0 := by

  change ambientPairing K (exteriorPower.ιMulti K 3 ![e K 0,e K 1,e K 2])
    (exteriorPower.ιMulti K 3 ![e K 0,e K 1,e K 2]) = 0
  exact pairing_zero_of_repeated_row K _ _ 0 3 (by decide) rfl

@[simp] theorem ambientPairing_b_b : ambientPairing K (b K) (b K) = 0 := by

  change ambientPairing K (exteriorPower.ιMulti K 3 ![f K 0,f K 1,f K 2])
    (exteriorPower.ιMulti K 3 ![f K 0,f K 1,f K 2]) = 0
  exact pairing_zero_of_repeated_row K _ _ 0 3 (by decide) rfl

set_option maxHeartbeats 4000000

@[simp] theorem ambientPairing_a_q (i j : Fin 3) : ambientPairing K (a K) (q K i j) = 0 := by

  change ambientPairing K (exteriorPower.ιMulti K 3 ![e K 0,e K 1,e K 2])
    (exteriorPower.ιMulti K 3 ![e K i,f K (nextOne j),f K (nextTwo j)]) = 0
  apply pairing_zero_of_repeated_row K _ _ (i.castAdd 3) 3
  · fin_cases i <;> decide
  · rw [Fin.append_left, left_basis_tuple]
    rfl

@[simp] theorem ambientPairing_a_p (i j : Fin 3) : ambientPairing K (a K) (p K i j) = 0 := by

  change ambientPairing K (exteriorPower.ιMulti K 3 ![e K 0,e K 1,e K 2])
    (exteriorPower.ιMulti K 3 ![f K i,e K (nextOne j),e K (nextTwo j)]) = 0
  apply pairing_zero_of_repeated_row K _ _ ((nextOne j).castAdd 3) 4
  · fin_cases j <;> decide
  · rw [Fin.append_left, left_basis_tuple]
    rfl

@[simp] theorem ambientPairing_b_q (i j : Fin 3) : ambientPairing K (b K) (q K i j) = 0 := by

  change ambientPairing K (exteriorPower.ιMulti K 3 ![f K 0,f K 1,f K 2])
    (exteriorPower.ιMulti K 3 ![e K i,f K (nextOne j),f K (nextTwo j)]) = 0
  apply pairing_zero_of_repeated_row K _ _ ((nextOne j).castAdd 3) 4
  · fin_cases j <;> decide
  · rw [Fin.append_left, right_basis_tuple]
    rfl

@[simp] theorem ambientPairing_b_p (i j : Fin 3) : ambientPairing K (b K) (p K i j) = 0 := by

  change ambientPairing K (exteriorPower.ιMulti K 3 ![f K 0,f K 1,f K 2])
    (exteriorPower.ιMulti K 3 ![f K i,e K (nextOne j),e K (nextTwo j)]) = 0
  apply pairing_zero_of_repeated_row K _ _ (i.castAdd 3) 3
  · fin_cases i <;> decide
  · rw [Fin.append_left, right_basis_tuple]
    rfl

@[simp] theorem ambientPairing_q_a (i j : Fin 3) : ambientPairing K (q K i j) (a K) = 0 := by
  rw [ambientPairing_neg_swap, ambientPairing_a_q, neg_zero]
@[simp] theorem ambientPairing_p_a (i j : Fin 3) : ambientPairing K (p K i j) (a K) = 0 := by
  rw [ambientPairing_neg_swap, ambientPairing_a_p, neg_zero]
@[simp] theorem ambientPairing_q_b (i j : Fin 3) : ambientPairing K (q K i j) (b K) = 0 := by
  rw [ambientPairing_neg_swap, ambientPairing_b_q, neg_zero]
@[simp] theorem ambientPairing_p_b (i j : Fin 3) : ambientPairing K (p K i j) (b K) = 0 := by
  rw [ambientPairing_neg_swap, ambientPairing_b_p, neg_zero]

@[simp] theorem ambientPairing_q_q (i j k l : Fin 3) :
    ambientPairing K (q K i j) (q K k l) = 0 := by

  change ambientPairing K (exteriorPower.ιMulti K 3
    ![e K i,f K (nextOne j),f K (nextTwo j)])
    (exteriorPower.ιMulti K 3
      ![e K k,f K (nextOne l),f K (nextTwo l)]) = 0
  rcases cyclic_pairs_intersect j l with h | h | h | h
  · apply pairing_zero_of_repeated_row K _ _ 1 4 (by decide)
    change f K (nextOne j) = f K (nextOne l)
    rw [h]
  · apply pairing_zero_of_repeated_row K _ _ 1 5 (by decide)
    change f K (nextOne j) = f K (nextTwo l)
    rw [h]
  · apply pairing_zero_of_repeated_row K _ _ 2 4 (by decide)
    change f K (nextTwo j) = f K (nextOne l)
    rw [h]
  · apply pairing_zero_of_repeated_row K _ _ 2 5 (by decide)
    change f K (nextTwo j) = f K (nextTwo l)
    rw [h]

@[simp] theorem ambientPairing_p_p (i j k l : Fin 3) :
    ambientPairing K (p K i j) (p K k l) = 0 := by

  change ambientPairing K (exteriorPower.ιMulti K 3
    ![f K i,e K (nextOne j),e K (nextTwo j)])
    (exteriorPower.ιMulti K 3
      ![f K k,e K (nextOne l),e K (nextTwo l)]) = 0
  rcases cyclic_pairs_intersect j l with h | h | h | h
  · apply pairing_zero_of_repeated_row K _ _ 1 4 (by decide)
    change e K (nextOne j) = e K (nextOne l)
    rw [h]
  · apply pairing_zero_of_repeated_row K _ _ 1 5 (by decide)
    change e K (nextOne j) = e K (nextTwo l)
    rw [h]
  · apply pairing_zero_of_repeated_row K _ _ 2 4 (by decide)
    change e K (nextTwo j) = e K (nextOne l)
    rw [h]
  · apply pairing_zero_of_repeated_row K _ _ 2 5 (by decide)
    change e K (nextTwo j) = e K (nextTwo l)
    rw [h]

private theorem pairing_q_p_diagonal (i j : Fin 3) :
    ambientPairing K (q K i j) (p K j i) = 1 := by
  let rotateE : Equiv.Perm (Fin 6) := Equiv.swap 1 2 * Equiv.swap 0 2
  let rotateF : Equiv.Perm (Fin 6) := Equiv.swap 4 5 * Equiv.swap 3 5
  let shuffle : Equiv.Perm (Fin 6) := Equiv.swap 2 5 * Equiv.swap 1 4
  let σ := rotateE ^ i.val * rotateF ^ j.val * shuffle
  have hsign : Equiv.Perm.sign σ = 1 := by
    simp [σ, rotateE, rotateF, shuffle, Equiv.Perm.sign_swap']
  have hrow : ∀ (x y : Fin 3) (r : Fin 6),
      Fin.append ![eIndex x, fIndex (nextOne y), fIndex (nextTwo y)]
        ![fIndex y, eIndex (nextOne x), eIndex (nextTwo x)] r =
      (rotateE ^ x.val * rotateF ^ y.val * shuffle) r := by
    dsimp only [rotateE, rotateF, shuffle]
    decide
  have hvector (r : Fin 6) :
      Fin.append ![e K i, f K (nextOne j), f K (nextTwo j)]
        ![f K j, e K (nextOne i), e K (nextTwo i)] r =
      basisVector K (Fin.append ![eIndex i, fIndex (nextOne j), fIndex (nextTwo j)]
        ![fIndex j, eIndex (nextOne i), eIndex (nextTwo i)] r) := by
    refine Fin.addCases (m := 3) (n := 3) ?_ ?_ r
    · intro t
      rw [Fin.append_left, Fin.append_left]
      fin_cases t <;> rfl
    · intro t
      rw [Fin.append_right, Fin.append_right]
      fin_cases t <;> rfl
  have hM : (Matrix.of fun r s : Fin 6 =>
      Fin.append ![e K i, f K (nextOne j), f K (nextTwo j)]
        ![f K j, e K (nextOne i), e K (nextTwo i)] r s) =
      (1 : Matrix (Fin 6) (Fin 6) K).submatrix σ id := by
    ext r s
    change Fin.append ![e K i, f K (nextOne j), f K (nextTwo j)]
      ![f K j, e K (nextOne i), e K (nextTwo i)] r s = (1 : Matrix (Fin 6) (Fin 6) K) (σ r) s
    rw [hvector, hrow, Matrix.one_apply]
    simp [σ, basisVector, Pi.single_apply, eq_comm]
  simp only [q, p, wedge3, ambientPairing_ιMulti]
  rw [hM, Matrix.det_permute, hsign]
  simp

/-- Full exterior mixed Gram matrix: it is the trace pairing, not the entrywise pairing. -/
@[simp] theorem ambientPairing_q_p (i j k l : Fin 3) :
    ambientPairing K (q K i j) (p K k l) = if i=l then if j=k then 1 else 0 else 0 := by

  by_cases hil : i = l
  · subst l
    by_cases hjk : j = k
    · subst k
      simp only [ite_true]
      exact pairing_q_p_diagonal K i j
    · simp only [ite_true, if_neg hjk]
      change ambientPairing K (exteriorPower.ιMulti K 3
        ![e K i,f K (nextOne j),f K (nextTwo j)])
        (exteriorPower.ιMulti K 3
          ![f K k,e K (nextOne i),e K (nextTwo i)]) = 0
      rcases cyclic_cases k j with h | h | h
      · exact (hjk h.symm).elim
      · apply pairing_zero_of_repeated_row K _ _ 1 3 (by decide)
        change f K (nextOne j) = f K k
        rw [h]
      · apply pairing_zero_of_repeated_row K _ _ 2 3 (by decide)
        change f K (nextTwo j) = f K k
        rw [h]
  · simp only [if_neg hil]
    change ambientPairing K (exteriorPower.ιMulti K 3
      ![e K i,f K (nextOne j),f K (nextTwo j)])
      (exteriorPower.ιMulti K 3
        ![f K k,e K (nextOne l),e K (nextTwo l)]) = 0
    rcases cyclic_cases i l with h | h | h
    · exact (hil h).elim
    · apply pairing_zero_of_repeated_row K _ _ 0 4 (by decide)
      change e K i = e K (nextOne l)
      rw [h]
    · apply pairing_zero_of_repeated_row K _ _ 0 5 (by decide)
      change e K i = e K (nextTwo l)
      rw [h]

@[simp] theorem ambientPairing_p_q (i j k l : Fin 3) :
    ambientPairing K (p K i j) (q K k l) = -(if k=j then if l=i then 1 else 0 else 0) := by
  rw [ambientPairing_neg_swap, ambientPairing_q_p]

@[simp] theorem ambientPairing_a_mixedQ (X : Matrix (Fin 3) (Fin 3) K) :
    ambientPairing K (a K) (mixedQ K X) = 0 := by simp [mixedQ]
@[simp] theorem ambientPairing_a_mixedP (X : Matrix (Fin 3) (Fin 3) K) :
    ambientPairing K (a K) (mixedP K X) = 0 := by simp [mixedP]
@[simp] theorem ambientPairing_b_mixedQ (X : Matrix (Fin 3) (Fin 3) K) :
    ambientPairing K (b K) (mixedQ K X) = 0 := by simp [mixedQ]
@[simp] theorem ambientPairing_b_mixedP (X : Matrix (Fin 3) (Fin 3) K) :
    ambientPairing K (b K) (mixedP K X) = 0 := by simp [mixedP]
@[simp] theorem ambientPairing_mixedQ_a (X : Matrix (Fin 3) (Fin 3) K) :
    ambientPairing K (mixedQ K X) (a K) = 0 := by rw [ambientPairing_neg_swap]; simp
@[simp] theorem ambientPairing_mixedP_a (X : Matrix (Fin 3) (Fin 3) K) :
    ambientPairing K (mixedP K X) (a K) = 0 := by rw [ambientPairing_neg_swap]; simp
@[simp] theorem ambientPairing_mixedQ_b (X : Matrix (Fin 3) (Fin 3) K) :
    ambientPairing K (mixedQ K X) (b K) = 0 := by rw [ambientPairing_neg_swap]; simp
@[simp] theorem ambientPairing_mixedP_b (X : Matrix (Fin 3) (Fin 3) K) :
    ambientPairing K (mixedP K X) (b K) = 0 := by rw [ambientPairing_neg_swap]; simp

@[simp] theorem ambientPairing_q_mixedP (i j : Fin 3) (Y : Matrix (Fin 3) (Fin 3) K) :
    ambientPairing K (q K i j) (mixedP K Y) = Y j i := by
  classical
  simp [mixedP, smul_eq_mul, mul_ite]

@[simp] theorem ambientPairing_mixedQ_mixedQ (X Y : Matrix (Fin 3) (Fin 3) K) :
    ambientPairing K (mixedQ K X) (mixedQ K Y) = 0 := by simp [mixedQ]
@[simp] theorem ambientPairing_mixedP_mixedP (X Y : Matrix (Fin 3) (Fin 3) K) :
    ambientPairing K (mixedP K X) (mixedP K Y) = 0 := by simp [mixedP]

@[simp] theorem ambientPairing_mixedQ_mixedP (X Y : Matrix (Fin 3) (Fin 3) K) :
    ambientPairing K (mixedQ K X) (mixedP K Y) = Matrix.trace (X * Y) := by
  simp [mixedQ, Matrix.trace, Matrix.diag, Matrix.mul_apply, smul_eq_mul]

@[simp] theorem ambientPairing_mixedP_mixedQ (X Y : Matrix (Fin 3) (Fin 3) K) :
    ambientPairing K (mixedP K X) (mixedQ K Y) = -Matrix.trace (Y * X) := by
  rw [ambientPairing_neg_swap, ambientPairing_mixedQ_mixedP]

/-- The actual wedge pairing pulls back to exactly the paper's trace-difference form. -/
theorem ambientPairing_embedding (r s : PrimitiveRepresentation.Coordinates K) :
    ambientPairing K (coordinateEmbedding K r) (coordinateEmbedding K s) =
      PrimitiveRepresentation.pairing K r s := by
  simp [coordinateEmbedding, Matrix.trace_sub, smul_eq_mul]
  ring

/-- Restriction of exterior multiplication and the actual volume to the actual primitive kernel. -/
def primitivePairing : LinearMap.BilinForm K (Primitive K) :=
  (ambientPairing K).compl₁₂ (Primitive K).subtype (Primitive K).subtype

@[simp] theorem primitivePairing_apply (u v : Primitive K) :
    primitivePairing K u v = ambientPairing K u.val v.val := rfl

@[simp] theorem primitivePairing_equiv [CharZero K] (r s : PrimitiveRepresentation.Coordinates K) :
    primitivePairing K (primitiveEquiv K r) (primitiveEquiv K s) =
      PrimitiveRepresentation.pairing K r s := ambientPairing_embedding K r s

theorem primitivePairing_neg_swap (u v : Primitive K) :
    primitivePairing K u v = -primitivePairing K v u := ambientPairing_neg_swap K u.val v.val

/-- The primitive restriction is an alternating bilinear form. -/
theorem primitivePairing_isAlt [CharZero K] : (primitivePairing K).IsAlt := by
  intro u
  obtain ⟨r, rfl⟩ := (primitiveEquiv K).surjective u
  simpa only [primitivePairing_equiv] using PrimitiveRepresentation.pairing_isAlt K r

theorem primitivePairing_separating_left [CharZero K] (u : Primitive K)
    (hu : ∀ v, primitivePairing K u v = 0) : u = 0 := by
  obtain ⟨r, rfl⟩ := (primitiveEquiv K).surjective u
  have hr : r = 0 := PrimitiveRepresentation.pairing_separating_left K r (fun s => by
    rw [← primitivePairing_equiv]
    exact hu _)
  simp [hr]

/-- Nondegeneracy refers to the actual exterior restriction, via the explicit proved isomorphism. -/
theorem primitivePairing_nondegenerate [CharZero K] : (primitivePairing K).Nondegenerate := by
  constructor
  · exact primitivePairing_separating_left K
  · intro u hu
    apply primitivePairing_separating_left K u
    intro v
    rw [primitivePairing_neg_swap, hu, neg_zero]

/-- Diagonal mixed basis vectors have Gram weight one. -/
@[simp] theorem ambientPairing_diagonal_weight (i : Fin 3) :
    ambientPairing K (q K i i) (p K i i) = 1 := by simp

/-- Symmetric off-diagonal mixed basis vectors have the manuscript's Gram weight two. -/
theorem ambientPairing_offDiagonal_weight (i j : Fin 3) (hij : i ≠ j) :
    ambientPairing K (q K i j + q K j i) (p K j i + p K i j) = 2 := by
  norm_num [hij, Ne.symm hij]


@[simp] theorem omega_pair_e (u : V K) (i : Fin 3) :
    omega K u (e K i) = -u (fIndex i) := by
  change omegaValue K u (e K i) = -u (fIndex i)
  fin_cases i <;>
    simp only [omegaValue, Fin.sum_univ_succ, e, basisVector, eIndex, fIndex] <;>
    norm_num [Pi.single_apply]

@[simp] theorem omega_pair_f (u : V K) (i : Fin 3) :
    omega K u (f K i) = u (eIndex i) := by
  change omegaValue K u (f K i) = u (eIndex i)
  fin_cases i <;>
    simp only [omegaValue, Fin.sum_univ_succ, f, basisVector, eIndex, fIndex] <;>
    norm_num [Pi.single_apply]

theorem omega_separating_left (u : V K) (hu : ∀ v, omega K u v = 0) : u = 0 := by
  have hE (j : Fin 3) : u (eIndex j) = 0 := by
    rw [← omega_pair_f K u j]
    exact hu _
  have hF (j : Fin 3) : u (fIndex j) = 0 := by
    have h := hu (e K j)
    rw [omega_pair_e, neg_eq_zero] at h
    exact h
  funext i
  exact Fin.addCases (motive := fun i : Fin 6 => u i = 0)
    (fun j => hE j) (fun j => hF j) i

/-- The six-dimensional input is equipped with the actual nondegenerate symplectic form. -/
theorem omega_nondegenerate : (omega K).Nondegenerate := by
  constructor
  · exact omega_separating_left K
  · intro u hu
    apply omega_separating_left K u
    intro v
    rw [omega_swap, hu, neg_zero]

@[simp] theorem omega_isAlt : (omega K).IsAlt := omega_self K


/-- Exterior multiplication is exactly the scalar pairing times the chosen actual volume. -/
theorem wedge_eq_pairing_smul_volume (x y : Third K) :
    exteriorPower.wedge K (V K) 3 3 x y = ambientPairing K x y • volume K := by
  apply (volumeEquiv K).injective
  change volumeCoordinate K (exteriorPower.wedge K (V K) 3 3 x y) =
    volumeCoordinate K (ambientPairing K x y • volume K)
  rw [map_smul, volumeCoordinate_volume, smul_eq_mul, mul_one]
  rfl

/-- The same volume identity in Mathlib's actual exterior algebra. -/
theorem mul_eq_pairing_smul_volume (x y : Third K) :
    (x : ExteriorAlgebra K (V K)) * (y : ExteriorAlgebra K (V K)) =
      ambientPairing K x y • (volume K : ExteriorAlgebra K (V K)) :=
  congrArg (fun z : ⋀[K]^6 (V K) => (z : ExteriorAlgebra K (V K)))
    (wedge_eq_pairing_smul_volume K x y)

end M9.ExteriorPrimitive
