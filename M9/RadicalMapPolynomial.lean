module

public import M9.RadicalMapProjective
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Basis.Defs

/-! # Literal polynomial formulas on the forty-five-coordinate Grassmannian chart -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace M9.RadicalMap

open Module Matrix
open scoped BigOperators

abbrev ChartIndex := Fin 5 × Fin 9
abbrev AmbientIndex := Fin 9 ⊕ Fin 5
abbrev ChartRing (K : Type*) [CommSemiring K] := MvPolynomial ChartIndex K

section Polynomial

variable (K : Type*) [Field K]

/-- The literal [I;X] frame of the standard Grassmannian chart. -/
def polynomialFrame : Matrix AmbientIndex (Fin 9) (ChartRing K) :=
  Sum.elim (fun i j => if i = j then 1 else 0) (fun a j => MvPolynomial.X (a,j))

/-- The literal polynomial Gram matrix of the chart frame. -/
def polynomialGram (J : Matrix AmbientIndex AmbientIndex K) : Matrix (Fin 9) (Fin 9) (ChartRing K) :=
  fun i j => ∑ a, ∑ b, polynomialFrame K a i * MvPolynomial.C (J a b) * polynomialFrame K b j

/-- Polynomial cofactor coordinates defining each principal radical chart. -/
def polynomialCofactor (J : Matrix AmbientIndex AmbientIndex K) (i j : Fin 9) : ChartRing K :=
  (polynomialGram K J).adjugate i j

/-- Literal homogeneous projective coordinates for the radical of the chart frame. -/
def polynomialRadical (J : Matrix AmbientIndex AmbientIndex K) (j : Fin 9) :
    AmbientIndex → ChartRing K :=
  polynomialFrame K *ᵥ kernelVector (polynomialGram K J) j

def chartFrameMatrix (x : ChartIndex → K) : Matrix AmbientIndex (Fin 9) K :=
  (polynomialFrame K).map (MvPolynomial.eval x)

@[simp] theorem chartFrameMatrix_inl (x : ChartIndex → K) (i j : Fin 9) :
    chartFrameMatrix K x (Sum.inl i) j = if i = j then 1 else 0 := by
  simp [chartFrameMatrix,polynomialFrame]

@[simp] theorem chartFrameMatrix_inr (x : ChartIndex → K) (a : Fin 5) (j : Fin 9) :
    chartFrameMatrix K x (Sum.inr a) j = x (a,j) := by
  simp [chartFrameMatrix,polynomialFrame]

theorem polynomialGram_transpose (J : Matrix AmbientIndex AmbientIndex K)
    (hJ : J.transpose = -J) : (polynomialGram K J).transpose = -polynomialGram K J := by
  apply Matrix.ext
  intro i j
  change (∑ a, ∑ b, polynomialFrame K a j * MvPolynomial.C (J a b) * polynomialFrame K b i) =
    -(∑ a, ∑ b, polynomialFrame K a i * MvPolynomial.C (J a b) * polynomialFrame K b j)
  rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have h : J b a = -J a b := congrFun (congrFun hJ a) b
  rw [h,map_neg]
  ring

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- The actual chart frame in any actual fourteen-dimensional based space. -/
def chartFrame (b : Basis AmbientIndex K V) (x : ChartIndex → K) (j : Fin 9) : V :=
  b.equivFun.symm (fun a => chartFrameMatrix K x a j)

@[simp] theorem basis_chartFrame (b : Basis AmbientIndex K V) (x : ChartIndex → K)
    (j : Fin 9) (a : AmbientIndex) :
    b.equivFun (chartFrame K b x j) a = chartFrameMatrix K x a j := by
  exact congrFun (b.equivFun.apply_symm_apply _) a

theorem basis_frameMap_chartFrame (b : Basis AmbientIndex K V) (x : ChartIndex → K)
    (v : Fin 9 → K) (a : AmbientIndex) :
    b.equivFun (frameMap (chartFrame K b x) v) a =
      (chartFrameMatrix K x *ᵥ v) a := by
  simp only [frameMap,Fintype.linearCombination_apply,map_sum,map_smul,Finset.sum_apply,
    Pi.smul_apply,smul_eq_mul,basis_chartFrame,Matrix.mulVec,dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Every actual [I;X] chart frame is independent, not an extra open-locus premise. -/
theorem chartFrame_independent (b : Basis AmbientIndex K V) (x : ChartIndex → K) :
    LinearIndependent K (chartFrame K b x) := by
  apply linearIndependent_iff_injective_fintypeLinearCombination.mpr
  intro v w h
  funext i
  have he := congrArg (fun z => b.equivFun z (Sum.inl i)) h
  change b.equivFun (frameMap (chartFrame K b x) v) (Sum.inl i) =
    b.equivFun (frameMap (chartFrame K b x) w) (Sum.inl i) at he
  simpa [basis_frameMap_chartFrame,Matrix.mulVec,dotProduct] using he

/-- Evaluation of the polynomial Gram matrix is the genuine restricted bilinear form. -/
theorem eval_polynomialGram (B : LinearMap.BilinForm K V) (b : Basis AmbientIndex K V)
    (x : ChartIndex → K) :
    (polynomialGram K (fun a c => B (b a) (b c))).map (MvPolynomial.eval x) =
      gram B (chartFrame K b x) := by
  ext i j
  simp only [Matrix.map_apply,polynomialGram,map_sum,map_mul,MvPolynomial.eval_C]
  rw [gram,chartFrame,chartFrame,Basis.equivFun_symm_apply,Basis.equivFun_symm_apply]
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,
    chartFrameMatrix,Matrix.map_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- The actual cofactor chart is the nonvanishing locus of a literal polynomial. -/
theorem eval_polynomialCofactor (B : LinearMap.BilinForm K V) (b : Basis AmbientIndex K V)
    (x : ChartIndex → K) (i j : Fin 9) :
    MvPolynomial.eval x (polynomialCofactor K (fun a c => B (b a) (b c)) i j) =
      (gram B (chartFrame K b x)).adjugate i j := by
  unfold polynomialCofactor
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix,Matrix.adjugate_fin_succ_eq_det_submatrix,
    map_mul,map_pow,map_neg,map_one]
  congr 1
  calc
    MvPolynomial.eval x
        ((polynomialGram K (fun a c => B (b a) (b c))).submatrix j.succAbove i.succAbove).det =
      (((polynomialGram K (fun a c => B (b a) (b c))).map (MvPolynomial.eval x)).submatrix
        j.succAbove i.succAbove).det := by
      rw [(MvPolynomial.eval x).map_det]
      rfl
    _ = _ := by rw [eval_polynomialGram K B b x]

/-- Evaluating the literal polynomial projective coordinates gives the actual radical vector. -/
theorem eval_polynomialRadical (B : LinearMap.BilinForm K V) (b : Basis AmbientIndex K V)
    (x : ChartIndex → K) (j : Fin 9) (a : AmbientIndex) :
    MvPolynomial.eval x (polynomialRadical K (fun a c => B (b a) (b c)) j a) =
      b.equivFun (radicalVector B (chartFrame K b x) j) a := by
  rw [radicalVector,basis_frameMap_chartFrame]
  simp only [polynomialRadical,Matrix.mulVec,dotProduct,map_sum,map_mul,kernelVector]
  apply Finset.sum_congr rfl
  intro i _
  rw [show MvPolynomial.eval x ((polynomialGram K (fun a c => B (b a) (b c))).adjugate i j) =
    (gram B (chartFrame K b x)).adjugate i j from eval_polynomialCofactor K B b x i j]
  rfl

section RankEight

variable [CharZero K]

/-- On the genuine affine Grassmannian chart the rank-eight domain is the union
of explicit principal nonzero-polynomial loci. -/
theorem rank_eight_iff_polynomialCofactor (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (b : Basis AmbientIndex K V) (x : ChartIndex → K) :
    (gram B (chartFrame K b x)).rank = 8 ↔
      ∃ i j, MvPolynomial.eval x (polynomialCofactor K (fun a c => B (b a) (b c)) i j) ≠ 0 := by
  simp only [eval_polynomialCofactor]
  exact rank_eight_iff_nonzero_cofactor _ (gram_transpose B hB _)

omit [CharZero K] in
/-- Every rank-eight point has a nonzero ambient polynomial radical component,
so ordinary projective affine charts cover the radical-map domain. -/
theorem exists_nonzero_polynomialRadical (B : LinearMap.BilinForm K V)
    (b : Basis AmbientIndex K V) (x : ChartIndex → K)
    (hr : (gram B (chartFrame K b x)).rank = 8) :
    ∃ j a, MvPolynomial.eval x (polynomialRadical K (fun a c => B (b a) (b c)) j a) ≠ 0 := by
  obtain ⟨i,j,hij⟩ := exists_nonzero_cofactor_of_rank_eight (gram B (chartFrame K b x)) hr
  have hn := radicalVector_ne_zero B (chartFrame K b x) (chartFrame_independent K b x) i j hij
  by_contra! hz
  apply hn
  apply b.equivFun.injective
  funext a
  rw [map_zero,Pi.zero_apply,← eval_polynomialRadical]
  exact hz j a

/-- A nonzero polynomial radical component automatically lies on the rank-eight domain. -/
theorem rank_eight_of_nonzero_polynomialRadical (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (b : Basis AmbientIndex K V) (x : ChartIndex → K) (j : Fin 9) (a : AmbientIndex)
    (hja : MvPolynomial.eval x (polynomialRadical K (fun a c => B (b a) (b c)) j a) ≠ 0) :
    (gram B (chartFrame K b x)).rank = 8 := by
  have hco : ∃ i, (gram B (chartFrame K b x)).adjugate i j ≠ 0 := by
    by_contra! hz
    have hk : kernelVector (gram B (chartFrame K b x)) j = 0 := funext hz
    have hv : radicalVector B (chartFrame K b x) j = 0 := by
      simp only [radicalVector,hk,map_zero]
    apply hja
    rw [eval_polynomialRadical,hv,map_zero,Pi.zero_apply]
  obtain ⟨i,hi⟩ := hco
  exact rank_eight_of_nonzero_cofactor _ (gram_transpose B hB _) i j hi

/-- The component opens are exactly a cover of the actual rank-eight Grassmannian chart. -/
theorem rank_eight_iff_polynomialRadical (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (b : Basis AmbientIndex K V) (x : ChartIndex → K) :
    (gram B (chartFrame K b x)).rank = 8 ↔
      ∃ j a, MvPolynomial.eval x (polynomialRadical K (fun a c => B (b a) (b c)) j a) ≠ 0 := by
  constructor
  · exact exists_nonzero_polynomialRadical K B b x
  · rintro ⟨j,a,hja⟩
    exact rank_eight_of_nonzero_polynomialRadical K B hB b x j a hja

/-- The explicit local polynomial formula equals the intrinsic projective radical map. -/
theorem chart_radicalPoint_formula (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (b : Basis AmbientIndex K V) (x : ChartIndex → K) (i j : Fin 9)
    (hij : MvPolynomial.eval x (polynomialCofactor K (fun a c => B (b a) (b c)) i j) ≠ 0) :
    let hr := rank_eight_of_nonzero_cofactor (gram B (chartFrame K b x))
      (gram_transpose B hB _) i j ((eval_polynomialCofactor K B b x i j) ▸ hij)
    radicalPoint B (framedPlane B hB (chartFrame K b x) (chartFrame_independent K b x) hr) =
      Projectivization.mk K (radicalVector B (chartFrame K b x) j)
        (radicalVector_ne_zero B _ (chartFrame_independent K b x) i j
          ((eval_polynomialCofactor K B b x i j) ▸ hij)) :=
  radicalPoint_eq_cofactor B hB _ (chartFrame_independent K b x) _ i j
    ((eval_polynomialCofactor K B b x i j) ▸ hij)

end RankEight

end Polynomial

end M9.RadicalMap
