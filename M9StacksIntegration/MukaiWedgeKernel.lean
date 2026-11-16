module

public import M9StacksIntegration.ExteriorEvaluation
public import M9StacksIntegration.MukaiSemiIrreducible
public import M9StacksIntegration.MukaiParityLinear
public import M9StacksIntegration.TupleEvaluationFiber
public import M9StacksIntegration.TupleEvaluationFiberRank
public import M9.IsotropicSandwichRank
public import M9.NondegeneratePencil
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# The actual exterior-evaluation kernel in Mukai's first step

Bivectors are represented by their genuine alternating coordinate matrices.
The pair and four-section fibre-rank exclusions are explicit geometric
hypotheses; they are not a nondegeneracy assumption on the exterior kernel.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace M9Native.MukaiWedgeKernel

open Module Matrix
open scoped BigOperators TensorProduct

section Bivectors

variable (k : Type*) [Field k] (n : ℕ)

abbrev Vector := Fin n → k
abbrev Bivector := ⋀[k]^2 (Vector k n)

/-- The genuine alternating map sending a pair of vectors to its skew matrix. -/
def wedgeMatrix : AlternatingMap k (Vector k n) (Matrix (Fin n) (Fin n) k) (Fin 2) where
  toFun v := vecMulVec (v 0) (v 1) - vecMulVec (v 1) (v 0)
  map_update_add' := by
    intro _ v i a b
    fin_cases i <;> funext r s <;>
      simp [vecMulVec_apply, Function.update] <;> ring
  map_update_smul' := by
    intro _ v i a b
    fin_cases i <;> funext r s <;>
      simp [vecMulVec_apply, Function.update] <;> ring
  map_eq_zero_of_eq' := by
    intro v i j hij hne
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · change v 0 = v 1 at hij
      rw [hij, sub_self]
    · change v 1 = v 0 at hij
      rw [hij, sub_self]
    · exact (hne rfl).elim

def bivectorMatrix : Bivector k n →ₗ[k] Matrix (Fin n) (Fin n) k :=
  exteriorPower.alternatingMapLinearEquiv (wedgeMatrix k n)

theorem bivectorMatrix_ιMulti (v : Fin 2 → Vector k n) :
    bivectorMatrix k n (exteriorPower.ιMulti k 2 v) =
      vecMulVec (v 0) (v 1) - vecMulVec (v 1) (v 0) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

def matrixEntry (i j : Fin n) : Matrix (Fin n) (Fin n) k →ₗ[k] k where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem bivectorMatrix_entry_pairing (w : Bivector k n) (i j : Fin n) :
    bivectorMatrix k n w i j =
      exteriorPower.pairingDual k (Vector k n) 2
        (exteriorPower.ιMulti k 2 ![(Pi.basisFun k (Fin n)).coord i, (Pi.basisFun k (Fin n)).coord j]) w := by
  have hh : (matrixEntry k n i j).comp (bivectorMatrix k n) =
      exteriorPower.pairingDual k (Vector k n) 2
        (exteriorPower.ιMulti k 2 ![(Pi.basisFun k (Fin n)).coord i, (Pi.basisFun k (Fin n)).coord j]) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, matrixEntry,
      bivectorMatrix_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti, Matrix.det_fin_two,
      Module.Basis.coord_apply, Pi.basisFun_repr, vecMulVec_apply]
    ring
  exact LinearMap.congr_fun hh w

theorem bivectorMatrix_injective : Function.Injective (bivectorMatrix k n) := by
  apply (bivectorMatrix k n).ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro w hw
  have hz : bivectorMatrix k n w = 0 := hw
  apply (Pi.basisFun k (Fin n)).exteriorPower 2 |>.repr.injective
  ext s
  rw [map_zero, Finsupp.zero_apply, exteriorPower.basis_repr_apply]
  let a := Set.powersetCard.ofFinEmbEquiv.symm s
  have ha : exteriorPower.ιMulti_family k 2 (Pi.basisFun k (Fin n)).coord s =
      exteriorPower.ιMulti k 2 ![(Pi.basisFun k (Fin n)).coord (a 0), (Pi.basisFun k (Fin n)).coord (a 1)] := by
    unfold exteriorPower.ιMulti_family
    congr 1
    funext i
    fin_cases i <;> rfl
  change exteriorPower.pairingDual k (Vector k n) 2
    (exteriorPower.ιMulti_family k 2 (Pi.basisFun k (Fin n)).coord s) w = 0
  rw [ha, ← bivectorMatrix_entry_pairing, hz]
  rfl

theorem bivectorMatrix_skew (w : Bivector k n) : (bivectorMatrix k n w)ᵀ = -bivectorMatrix k n w := by
  have hh : (Matrix.transposeLinearEquiv (Fin n) (Fin n) k k).toLinearMap.comp (bivectorMatrix k n) =
      -(bivectorMatrix k n) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    funext i j
    simp [LinearMap.compAlternatingMap_apply, bivectorMatrix_ιMulti, vecMulVec_apply]
    ring
  exact LinearMap.congr_fun hh w

theorem rank_eq_finrank_bilinear (B : Matrix (Fin n) (Fin n) k) :
    B.rank = finrank k (LinearMap.range B.toBilin') := by
  let b := Pi.basisFun k (Fin n)
  have hm : LinearMap.toMatrix b b.dualBasis B.toBilin' = Bᵀ := by
    funext i j
    simp [LinearMap.toMatrix_apply, Module.Basis.dualBasis_repr, b, Pi.basisFun_apply]
  have hr := Matrix.rank_eq_finrank_range_toLin
    (LinearMap.toMatrix b b.dualBasis B.toBilin') b.dualBasis b
  rw [Matrix.toLin_toMatrix, hm, Matrix.rank_transpose] at hr
  exact hr

theorem skew_isAlt [CharZero k] (B : Matrix (Fin n) (Fin n) k) (hB : Bᵀ = -B) : B.toBilin'.IsAlt := by
  intro v
  have hentry (i j : Fin n) : B j i = -B i j := congrFun (congrFun hB i) j
  have hneg : B.toBilin' v v = -B.toBilin' v v := by
    simp only [Matrix.toBilin'_apply]
    rw [← Finset.sum_neg_distrib]
    calc
      ∑ i, ∑ j, v i * B i j * v j = ∑ i, ∑ j, -(v j * B j i * v i) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hentry]
        ring
      _ = ∑ i, -(∑ j, v j * B j i * v i) := by simp only [Finset.sum_neg_distrib]
      _ = ∑ i, -(∑ j, v i * B i j * v j) := by
        have hc : (∑ i, ∑ j, v j * B j i * v i) = ∑ i, ∑ j, v i * B i j * v j := by
          rw [Finset.sum_comm]
        simpa only [Finset.sum_neg_distrib] using congrArg (fun t : k => -t) hc
  have hz : (2 : k) * B.toBilin' v v = 0 := by
    rw [two_mul]
    exact eq_neg_iff_add_eq_zero.mp hneg
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem even_rank_of_skew [CharZero k] (B : Matrix (Fin n) (Fin n) k) (hB : Bᵀ = -B) : Even B.rank := by
  rw [rank_eq_finrank_bilinear]
  exact MukaiParityLinear.even_finrank_range_alternating B.toBilin' (skew_isAlt k n B hB)

theorem rank_pos_of_matrix_ne_zero (B : Matrix (Fin n) (Fin n) k) (hB : B ≠ 0) : 0 < B.rank := by
  by_contra h
  have hr : finrank k (LinearMap.range B.mulVecLin) = 0 := Nat.eq_zero_of_not_pos h
  have hf : B.mulVecLin = 0 := LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hr)
  apply hB
  funext i j
  have hh := congrArg (fun f : (Fin n → k) →ₗ[k] (Fin n → k) => f (Pi.single j 1) i) hf
  simpa using hh

theorem rank_six_cases [CharZero k] (w : Bivector k 6) (hw : w ≠ 0) :
    (bivectorMatrix k 6 w).rank = 2 ∨ (bivectorMatrix k 6 w).rank = 4 ∨
      (bivectorMatrix k 6 w).rank = 6 := by
  have hne : bivectorMatrix k 6 w ≠ 0 := by
    intro h
    apply hw
    exact (bivectorMatrix_injective k 6) (h.trans (map_zero _).symm)
  have hp := rank_pos_of_matrix_ne_zero k 6 _ hne
  have hb := Matrix.rank_le_card_width (bivectorMatrix k 6 w)
  obtain ⟨a,ha⟩ := even_rank_of_skew k 6 _ (bivectorMatrix_skew k 6 w)
  simp only [Fintype.card_fin] at hb
  omega

end Bivectors

section Support

variable {k L : Type*} [Field k] [Field L] {n r m : ℕ}

abbrev support (B : Matrix (Fin n) (Fin n) k) := LinearMap.range B.mulVecLin

def supportColumn (B : Matrix (Fin n) (Fin n) k) (j : Fin n) : support B :=
  ⟨B.col j, ⟨Pi.single j 1, by simp⟩⟩

def supportInclusion (B : Matrix (Fin n) (Fin n) k) (b : Basis (Fin r) k (support B)) :
    Matrix (Fin n) (Fin r) k := fun i j => (b j).val i

def supportCoordinates (B : Matrix (Fin n) (Fin n) k) (b : Basis (Fin r) k (support B)) :
    Matrix (Fin r) (Fin n) k := fun i j => b.repr (supportColumn B j) i

theorem support_factorization (B : Matrix (Fin n) (Fin n) k) (b : Basis (Fin r) k (support B)) :
    supportInclusion B b * supportCoordinates B b = B := by
  funext i j
  have h := congrArg (fun v : support B => v.val i) (b.sum_repr (supportColumn B j))
  change (∑ a, (b a).val i * b.repr (supportColumn B j) a) = B i j
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, supportColumn, mul_comm, Matrix.col_apply] using h

def supportPreimages (B : Matrix (Fin n) (Fin n) k) (b : Basis (Fin r) k (support B)) :
    Matrix (Fin n) (Fin r) k := fun i j => Classical.choose (b j).property i

theorem support_preimages (B : Matrix (Fin n) (Fin n) k) (b : Basis (Fin r) k (support B)) :
    B * supportPreimages B b = supportInclusion B b := by
  funext i j
  exact congrFun (Classical.choose_spec (b j).property) i

theorem support_sections_independent (B : Matrix (Fin n) (Fin n) k) (b : Basis (Fin r) k (support B)) :
    LinearIndependent k (fun i => (b i).val) :=
  b.linearIndependent.map' (support B).subtype (by simp)

theorem mapped_support_rank_le (φ : k →+* L) (B : Matrix (Fin n) (Fin n) k)
    (b : Basis (Fin r) k (support B)) : (B.map φ).rank ≤ r := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) k => M.map φ)
    (support_factorization B b)
  rw [Matrix.map_mul] at h
  change (supportInclusion B b).map φ * (supportCoordinates B b).map φ = B.map φ at h
  rw [← h]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_width _)

theorem rank_support_eval_le_product (φ : k →+* L) (A : Matrix (Fin m) (Fin n) L)
    (B : Matrix (Fin n) (Fin n) k) (b : Basis (Fin r) k (support B)) :
    (A * (supportInclusion B b).map φ).rank ≤ (A * B.map φ).rank := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin r) k => M.map φ)
    (support_preimages B b)
  rw [Matrix.map_mul] at h
  change B.map φ * (supportPreimages B b).map φ = (supportInclusion B b).map φ at h
  rw [← h, ← Matrix.mul_assoc]
  exact Matrix.rank_mul_le_left _ _

/-- The support is the actual range of the bivector matrix. Its fibre image
has at most half its dimension whenever the genuine exterior image vanishes. -/
theorem two_mul_rank_support_eval_le (φ : k →+* L) (A : Matrix (Fin m) (Fin n) L)
    (B : Matrix (Fin n) (Fin n) k) (b : Basis (Fin r) k (support B))
    (hB : Bᵀ = -B) (hzero : A * B.map φ * Aᵀ = 0) :
    2 * (A * (supportInclusion B b).map φ).rank ≤ r := by
  have hskew : (B.map φ)ᵀ = -(B.map φ) := by
    funext i j
    exact (congrArg φ (congrFun (congrFun hB i) j)).trans (map_neg φ (B i j))
  have h := M9.IsotropicSandwichRank.two_mul_rank_product_le_of_skew_sandwich_zero A (B.map φ) hskew hzero
  have h₁ := mapped_support_rank_le φ B b
  have h₂ := rank_support_eval_le_product φ A B b
  omega

end Support

section ExteriorNaturality

variable {k L : Type*} [Field k] [Field L] {n m : ℕ}

def coefficientVectorMap (φ : k →+* L) : Vector k n →ₛₗ[φ] Vector L n where
  toFun v i := φ (v i)
  map_add' v w := by funext i; exact map_add φ _ _
  map_smul' c v := by funext i; exact map_mul φ _ _

def matrixEvaluation (φ : k →+* L) (A : Matrix (Fin m) (Fin n) L) :
    Vector k n →ₛₗ[φ] Vector L m := A.mulVecLin.comp (coefficientVectorMap φ)

def coefficientMatrixMap (φ : k →+* L) : Matrix (Fin n) (Fin n) k →ₛₗ[φ] Matrix (Fin n) (Fin n) L where
  toFun M := M.map φ
  map_add' M N := by funext i j; exact map_add φ _ _
  map_smul' c M := by funext i j; exact map_mul φ _ _

def sandwichLinear (A : Matrix (Fin m) (Fin n) L) :
    Matrix (Fin n) (Fin n) L →ₗ[L] Matrix (Fin m) (Fin m) L where
  toFun M := A * M * Aᵀ
  map_add' M N := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c M := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

/-- Exterior evaluation is literally the skew-matrix sandwich, including
the actual field embedding into a residue or geometric-point field. -/
theorem bivectorMatrix_naturality (φ : k →+* L) (A : Matrix (Fin m) (Fin n) L) (w : Bivector k n) :
    bivectorMatrix L m (ExteriorAlgebra.powMapₛₗ 2 φ (matrixEvaluation φ A) w) =
      A * (bivectorMatrix k n w).map φ * Aᵀ := by
  have hh : (bivectorMatrix L m).comp (ExteriorAlgebra.powMapₛₗ 2 φ (matrixEvaluation φ A)) =
      ((sandwichLinear A).comp (coefficientMatrixMap φ)).comp (bivectorMatrix k n) := by
    apply ExteriorAlgebra.powMapₛₗ_ext
    intro v
    change bivectorMatrix L m
      (ExteriorAlgebra.powMapₛₗ 2 φ (matrixEvaluation φ A) (exteriorPower.ιMulti k 2 v)) = _
    rw [ExteriorAlgebra.powMapₛₗ_ιMulti, bivectorMatrix_ιMulti]
    change vecMulVec (matrixEvaluation φ A (v 0)) (matrixEvaluation φ A (v 1)) -
      vecMulVec (matrixEvaluation φ A (v 1)) (matrixEvaluation φ A (v 0)) =
        A * (bivectorMatrix k n (exteriorPower.ιMulti k 2 v)).map φ * Aᵀ
    rw [bivectorMatrix_ιMulti]
    have hm (u v : Vector k n) : (vecMulVec u v).map φ =
        vecMulVec (fun i => φ (u i)) (fun i => φ (v i)) := by
      funext i j
      exact map_mul φ _ _
    have hs (M N : Matrix (Fin n) (Fin n) k) : (M-N).map φ = M.map φ - N.map φ := by
      funext i j
      exact map_sub φ _ _
    rw [hs, hm, hm, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_vecMulVec,
      Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul,
      Matrix.vecMul_transpose, Matrix.vecMul_transpose]
    rfl
  exact LinearMap.congr_fun hh w

theorem sandwich_zero_of_exterior_zero (φ : k →+* L) (A : Matrix (Fin m) (Fin n) L) (w : Bivector k n)
    (hw : ExteriorAlgebra.powMapₛₗ 2 φ (matrixEvaluation φ A) w = 0) :
    A * (bivectorMatrix k n w).map φ * Aᵀ = 0 := by
  rw [← bivectorMatrix_naturality, hw, map_zero]

end ExteriorNaturality

section MatrixFamilies

variable {k : Type*} [Field k] [CharZero k]
variable {P : Type*} (F : P → Type*) [∀ x, Field (F x)]
variable (φ : ∀ x, k →+* F x) (A : ∀ x, Matrix (Fin 3) (Fin 6) (F x))

def sectionMatrix {r : ℕ} (s : Fin r → Vector k 6) : Matrix (Fin 6) (Fin r) k := fun i j => s j i

/-- The actual pointwise rank exclusion on a family of section-evaluation matrices. -/
def MatrixSectionExclusion (r bound : ℕ) : Prop :=
  ∀ s : Fin r → Vector k 6, LinearIndependent k s →
    ∃ x : P, bound ≤ (A x * (sectionMatrix s).map (φ x)).rank

theorem matrix_det_ne_zero_of_exterior_vanishing
    (hpairs : MatrixSectionExclusion F φ A 2 2)
    (hfour : MatrixSectionExclusion F φ A 4 3)
    (w : Bivector k 6) (hw : w ≠ 0)
    (hzero : ∀ x : P, ExteriorAlgebra.powMapₛₗ 2 (φ x) (matrixEvaluation (φ x) (A x)) w = 0) :
    (bivectorMatrix k 6 w).det ≠ 0 := by
  let B := bivectorMatrix k 6 w
  have hB : Bᵀ = -B := bivectorMatrix_skew k 6 w
  have hs (x : P) : A x * B.map (φ x) * (A x)ᵀ = 0 :=
    sandwich_zero_of_exterior_zero (φ x) (A x) w (hzero x)
  rcases rank_six_cases k w hw with h2 | h4 | h6
  · let b : Basis (Fin 2) k (support B) :=
      (Module.finBasis k (support B)).reindex (finCongr h2)
    obtain ⟨x,hx⟩ := hpairs (fun i => (b i).val) (support_sections_independent B b)
    have hb := two_mul_rank_support_eval_le (φ x) (A x) B b hB (hs x)
    change 2 ≤ (A x * (supportInclusion B b).map (φ x)).rank at hx
    omega
  · let b : Basis (Fin 4) k (support B) :=
      (Module.finBasis k (support B)).reindex (finCongr h4)
    obtain ⟨x,hx⟩ := hfour (fun i => (b i).val) (support_sections_independent B b)
    have hb := two_mul_rank_support_eval_le (φ x) (A x) B b hB (hs x)
    change 3 ≤ (A x * (supportInclusion B b).map (φ x)).rank at hx
    omega
  · have hsurj : Function.Surjective B.mulVec :=
      Matrix.mulVec_surjective_iff_rank_eq_card.mpr (by simpa using h6)
    exact (Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.mulVec_surjective_iff_isUnit.mp hsurj) |>.ne_zero

end MatrixFamilies

section SemilinearCoordinates

variable {k L : Type*} [Field k] [Field L] {n m : ℕ} (φ : k →+* L)

def semilinearMatrix (g : Vector k n →ₛₗ[φ] Vector L m) : Matrix (Fin m) (Fin n) L :=
  fun i j => g (Pi.single j 1) i

theorem matrixEvaluation_semilinearMatrix (g : Vector k n →ₛₗ[φ] Vector L m) :
    matrixEvaluation φ (semilinearMatrix φ g) = g := by
  apply LinearMap.ext
  intro v
  have hg := congrArg g ((Pi.basisFun k (Fin n)).sum_repr v)
  simp only [map_sum, map_smulₛₗ, Pi.basisFun_repr, Pi.basisFun_apply] at hg
  rw [← hg]
  funext i
  simp [matrixEvaluation, LinearMap.comp_apply, coefficientVectorMap, semilinearMatrix,
    Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

end SemilinearCoordinates

section NativeEvaluation

open AlgebraicGeometry CategoryTheory

universe u
variable {X : Scheme.{u}} (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) (E : X.Modules)

abbrev Sections := cohomologyOverField k f E 0
abbrev LambdaTwo := ExteriorEvaluation.lambda k f E 2

/-- The precise native pair/four-section input used by the rank exclusions.
For rank three these are consequences of the subbundle bounds in Mukai
Proposition 3.5, not the raw rank-two or rank-four semi-irreducibility predicate. -/
def SectionRankExclusion (r bound : ℕ) : Prop :=
  ∀ s : Fin r → Sections k f E, LinearIndependent k s →
    ∃ x : X, bound ≤ MukaiSemiIrreducible.mapRankAt (MukaiSemiIrreducible.evaluation k f E s) x

variable (b : Basis (Fin 6) k (Sections k f E))

def coordinateBivector : (⋀[k]^2 (Sections k f E)) →ₗ[k] Bivector k 6 :=
  exteriorPower.map 2 b.equivFun.toLinearMap

theorem coordinateBivector_injective : Function.Injective (coordinateBivector k f E b) :=
  exteriorPower.map_injective_field b.equivFun.injective

def kernelMatrix : (⋀[k]^2 (Sections k f E)) →ₗ[k] Matrix (Fin 6) (Fin 6) k :=
  (bivectorMatrix k 6).comp (coordinateBivector k f E b)

theorem kernelMatrix_injective : Function.Injective (kernelMatrix k f E b) :=
  (bivectorMatrix_injective k 6).comp (coordinateBivector_injective k f E b)

variable [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]

def coordinateFiberEvaluation (x : X) :
    Vector k 6 →ₛₗ[TupleEvaluationFiber.residueBaseRingMap k f x] Vector (X.residueField x) 3 :=
  (TupleEvaluationFiber.fiberBasis E 3 x).equivFun.toLinearMap.comp
    ((TupleEvaluationFiber.sectionValue k f E x).comp b.equivFun.symm.toLinearMap)

def fiberMatrix (x : X) : Matrix (Fin 3) (Fin 6) (X.residueField x) :=
  semilinearMatrix (TupleEvaluationFiber.residueBaseRingMap k f x) (coordinateFiberEvaluation k f E b x)

theorem coordinateFiberEvaluation_eq_matrix (x : X) :
    coordinateFiberEvaluation k f E b x =
      matrixEvaluation (TupleEvaluationFiber.residueBaseRingMap k f x) (fiberMatrix k f E b x) :=
  (matrixEvaluation_semilinearMatrix _ _).symm

/-- A vector killed by the actual native `λ₂` is killed by exterior
evaluation in each actual residue-field fibre, expressed in genuine bases. -/
theorem coordinate_fiber_exterior_zero (x : X) (w : ⋀[k]^2 (Sections k f E))
    (hw : LambdaTwo k f E w = 0) :
    ExteriorAlgebra.powMapₛₗ 2 (TupleEvaluationFiber.residueBaseRingMap k f x)
      (matrixEvaluation (TupleEvaluationFiber.residueBaseRingMap k f x) (fiberMatrix k f E b x))
        (coordinateBivector k f E b w) = 0 := by
  let := TupleEvaluationFiber.residueAlgebra x
  have hz := ExteriorEvaluation.fiber_exterior_eq_zero_of_lambda_eq_zero k f x (X.residueField x) E 2 w hw
  have h :
      (ExteriorAlgebra.powMapₛₗ 2 (TupleEvaluationFiber.residueBaseRingMap k f x)
        (coordinateFiberEvaluation k f E b x)).comp (coordinateBivector k f E b) =
      (exteriorPower.map 2 (TupleEvaluationFiber.fiberBasis E 3 x).equivFun.toLinearMap).comp
        (ExteriorAlgebra.powMapₛₗ 2 (TupleEvaluationFiber.residueBaseRingMap k f x)
          (TupleEvaluationFiber.sectionValue k f E x)) := by
    apply ExteriorAlgebra.powMapₛₗ_ext
    intro s
    simp only [LinearMap.comp_apply, coordinateBivector, exteriorPower.map_apply_ιMulti,
      ExteriorAlgebra.powMapₛₗ_ιMulti]
    congr 1
    funext i
    change (TupleEvaluationFiber.fiberBasis E 3 x).equivFun
        (TupleEvaluationFiber.sectionValue k f E x (b.equivFun.symm (b.equivFun (s i)))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have hc := LinearMap.congr_fun h w
  change ExteriorAlgebra.powMapₛₗ 2 (TupleEvaluationFiber.residueBaseRingMap k f x)
    (coordinateFiberEvaluation k f E b x) (coordinateBivector k f E b w) =
      exteriorPower.map 2 (TupleEvaluationFiber.fiberBasis E 3 x).equivFun.toLinearMap
        (ExteriorAlgebra.powMapₛₗ 2 (TupleEvaluationFiber.residueBaseRingMap k f x)
          (TupleEvaluationFiber.sectionValue k f E x) w) at hc
  rw [show ExteriorAlgebra.powMapₛₗ 2 (TupleEvaluationFiber.residueBaseRingMap k f x)
    (TupleEvaluationFiber.sectionValue k f E x) w = 0 from hz, map_zero] at hc
  rw [coordinateFiberEvaluation_eq_matrix] at hc
  exact hc

theorem tuple_rank_in_coordinates {r : ℕ} (s : Fin r → Vector k 6) (x : X) :
    MukaiSemiIrreducible.mapRankAt
      (MukaiSemiIrreducible.evaluation k f E (fun i => b.equivFun.symm (s i))) x =
        (fiberMatrix k f E b x * (sectionMatrix s).map (TupleEvaluationFiber.residueBaseRingMap k f x)).rank := by
  rw [TupleEvaluationFiber.mapRankAt_evaluation_eq_finrank_tupleMap]
  let T := TupleEvaluationFiber.tupleMap k f E (fun i => b.equivFun.symm (s i)) x
  let c := TupleEvaluationFiber.fiberBasis E 3 x
  have hm : LinearMap.toMatrix (Pi.basisFun (X.residueField x) (Fin r)) c T =
      fiberMatrix k f E b x * (sectionMatrix s).map (TupleEvaluationFiber.residueBaseRingMap k f x) := by
    funext i j
    rw [LinearMap.toMatrix_apply]
    change c.repr (T ((Pi.basisFun (X.residueField x) (Fin r)) j)) i = _
    rw [Pi.basisFun_apply, show T (Pi.single j 1) =
      TupleEvaluationFiber.sectionValue k f E x (b.equivFun.symm (s j)) from
        TupleEvaluationFiber.tupleMap_single k f E _ x j]
    change coordinateFiberEvaluation k f E b x (s j) i =
      matrixEvaluation (TupleEvaluationFiber.residueBaseRingMap k f x)
        (semilinearMatrix _ (coordinateFiberEvaluation k f E b x)) (s j) i
    exact (congrFun (LinearMap.congr_fun (matrixEvaluation_semilinearMatrix _ _) (s j)) i).symm
  have hr := Matrix.rank_eq_finrank_range_toLin
    (LinearMap.toMatrix (Pi.basisFun (X.residueField x) (Fin r)) c T) c (Pi.basisFun _ (Fin r))
  rw [Matrix.toLin_toMatrix, hm] at hr
  exact hr.symm

/-- Every nonzero vector in the actual exterior-evaluation kernel is
nondegenerate. The hypotheses concern actual evaluation ranks of independent
section tuples, and do not supply any conclusion about this kernel. -/
theorem lambdaTwo_kernel_nondegenerate [CharZero k]
    (hpairs : SectionRankExclusion k f E 2 2) (hfour : SectionRankExclusion k f E 4 3)
    (w : ⋀[k]^2 (Sections k f E)) (hw : w ≠ 0) (h_lambda : LambdaTwo k f E w = 0) :
    (kernelMatrix k f E b w).det ≠ 0 := by
  have hp : MatrixSectionExclusion (fun x : X => X.residueField x)
      (TupleEvaluationFiber.residueBaseRingMap k f) (fiberMatrix k f E b) 2 2 := by
    intro s hs
    have ht : LinearIndependent k (fun i => b.equivFun.symm (s i)) :=
      hs.map' b.equivFun.symm.toLinearMap (by simp)
    obtain ⟨x,hx⟩ := hpairs _ ht
    exact ⟨x, by rwa [tuple_rank_in_coordinates] at hx⟩
  have hf : MatrixSectionExclusion (fun x : X => X.residueField x)
      (TupleEvaluationFiber.residueBaseRingMap k f) (fiberMatrix k f E b) 4 3 := by
    intro s hs
    have ht : LinearIndependent k (fun i => b.equivFun.symm (s i)) :=
      hs.map' b.equivFun.symm.toLinearMap (by simp)
    obtain ⟨x,hx⟩ := hfour _ ht
    exact ⟨x, by rwa [tuple_rank_in_coordinates] at hx⟩
  have hn : coordinateBivector k f E b w ≠ 0 := by
    intro hz
    apply hw
    exact (coordinateBivector_injective k f E b) (hz.trans (map_zero _).symm)
  exact matrix_det_ne_zero_of_exterior_vanishing _ _ _ hp hf
    (coordinateBivector k f E b w) hn (fun x => coordinate_fiber_exterior_zero k f E b x w h_lambda)

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank E 3] in
def kernelMatrixRestriction : (LambdaTwo k f E).ker →ₗ[k] Matrix (Fin 6) (Fin 6) k :=
  (kernelMatrix k f E b).comp (LambdaTwo k f E).ker.subtype

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank E 3] in
theorem kernelMatrixRestriction_injective : Function.Injective (kernelMatrixRestriction k f E b) :=
  (kernelMatrix_injective k f E b).comp (Submodule.subtype_injective _)

end NativeEvaluation

section KernelLine

open AlgebraicGeometry CategoryTheory

universe u
variable {X : Scheme.{u}} (k : Type u) [Field k] [CharZero k] [IsAlgClosed k]
  (f : X ⟶ Spec (.of k)) (E : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
  [FiniteDimensional k (Sections k f E)]
  [FiniteDimensional k (cohomologyOverField k f (Scheme.Modules.exteriorPower E 2) 0)]

/-- Mukai Step 1 for the genuine native `λ₂`: its kernel is a line and the
map is surjective once the actual H0 dimensions and pair/four exclusions
have been established. -/
theorem lambdaTwo_kernel_line_and_surjective
    (hsections : finrank k (Sections k f E) = 6)
    (hexterior : finrank k (cohomologyOverField k f (Scheme.Modules.exteriorPower E 2) 0) = 14)
    (hpairs : SectionRankExclusion k f E 2 2) (hfour : SectionRankExclusion k f E 4 3) :
    finrank k (LambdaTwo k f E).ker = 1 ∧ Function.Surjective (LambdaTwo k f E) := by
  let b : Basis (Fin 6) k (Sections k f E) :=
    (Module.finBasis k (Sections k f E)).reindex (finCongr hsections)
  have hd : finrank k (⋀[k]^2 (Sections k f E)) =
      finrank k (cohomologyOverField k f (Scheme.Modules.exteriorPower E 2) 0) + 1 := by
    rw [exteriorPower.finrank_eq, hsections, hexterior]
    decide
  apply M9.NondegeneratePencil.kernel_line_and_surjective (LambdaTwo k f E) hd
    (kernelMatrixRestriction k f E b) (kernelMatrixRestriction_injective k f E b)
  intro v hv
  have hn : v.val ≠ 0 := by
    intro hz
    apply hv
    exact Subtype.ext hz
  exact lambdaTwo_kernel_nondegenerate k f E b hpairs hfour v.val hn v.property

end KernelLine

end M9Native.MukaiWedgeKernel
