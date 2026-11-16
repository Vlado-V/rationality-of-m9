module

public import M9.PrimitiveStabilizer
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# A genuine symplectic Gauss family near the split primitive three-vector

The family is built on the actual six-dimensional vector space. Its matrix is
scaled by the torus parameter, so all entries are polynomial. Normalization at
a nonzero parameter yields an actual member of the symplectic group.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9.PrimitiveOpenOrbit

open Module Matrix ExteriorPrimitive PrimitiveStabilizer
open scoped BigOperators

variable (K : Type*) [Field K]

abbrev W := Fin 3 → K
abbrev Split := W K × W K

/-- Upper symplectic shear on the actual split vector space. -/
def upperSplit (B : Symmetric3 K) : Split K →ₗ[K] Split K :=
  ((LinearMap.fst K (W K) (W K)) +
    (Matrix.toLin' B.val).comp (LinearMap.snd K (W K) (W K))).prod
      (LinearMap.snd K (W K) (W K))

/-- Lower symplectic shear on the actual split vector space. -/
def lowerSplit (C : Symmetric3 K) : Split K →ₗ[K] Split K :=
  (LinearMap.fst K (W K) (W K)).prod
    ((Matrix.toLin' C.val).comp (LinearMap.fst K (W K) (W K)) +
      (LinearMap.snd K (W K) (W K)))

@[simp] theorem upperSplit_apply (B : Symmetric3 K) (v : Split K) :
    upperSplit K B v = (v.1 + B.val *ᵥ v.2, v.2) := rfl
@[simp] theorem lowerSplit_apply (C : Symmetric3 K) (v : Split K) :
    lowerSplit K C v = (v.1, C.val *ᵥ v.1 + v.2) := rfl

/-- Diagonal scalar multiplication on a three-dimensional coordinate space. -/
def coordinateDiagonal (d : Fin 3 → K) : W K →ₗ[K] W K :=
  LinearMap.pi fun i => d i • (LinearMap.proj i : W K →ₗ[K] K)

@[simp] theorem coordinateDiagonal_apply (d : Fin 3 → K) (v : W K) (i : Fin 3) :
    coordinateDiagonal K d v i = d i * v i := rfl

/-- This polynomial diagonal is `t` times `diag(t,1,1,t⁻¹,1,1)`. -/
def scaledDiagonalSplit (t : K) : Split K →ₗ[K] Split K :=
  ((coordinateDiagonal K ![t^2,t,t]).comp (LinearMap.fst K (W K) (W K))).prod
    ((coordinateDiagonal K ![1,t,t]).comp (LinearMap.snd K (W K) (W K)))

@[simp] theorem scaledDiagonalSplit_apply (t : K) (v : Split K) :
    scaledDiagonalSplit K t v =
      (coordinateDiagonal K ![t^2,t,t] v.1, coordinateDiagonal K ![1,t,t] v.2) := rfl

/-- Transport a literal split linear map to the actual ordered six-dimensional space. -/
def onV (f : Split K →ₗ[K] Split K) : V K →ₗ[K] V K :=
  (splitV K).symm.toLinearMap.comp (f.comp (splitV K).toLinearMap)

@[simp] theorem split_onV (f : Split K →ₗ[K] Split K) (v : V K) :
    splitV K (onV K f v) = f (splitV K v) := by simp [onV]

/-- The denominator-free actual Gauss family `t·u(B)d(t)l(C)`. -/
def scaledGauss (t : K) (B C : Symmetric3 K) : V K →ₗ[K] V K :=
  onV K ((upperSplit K B).comp ((scaledDiagonalSplit K t).comp (lowerSplit K C)))

@[simp] theorem split_scaledGauss (t : K) (B C : Symmetric3 K) (v : V K) :
    splitV K (scaledGauss K t B C v) =
      upperSplit K B (scaledDiagonalSplit K t (lowerSplit K C (splitV K v))) := by
  simp [scaledGauss]

theorem symmetric_dot (B : Symmetric3 K) (u v : W K) :
    (B.val *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (B.val *ᵥ v) := by
  rw [dotProduct_comm]
  have hB : B.val.transpose = B.val := B.property
  simpa only [hB] using (dotProduct_transpose_mulVec B.val u v).symm

def splitOmega (u v : Split K) : K := u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1

@[simp] theorem splitOmega_upper (B : Symmetric3 K) (u v : Split K) :
    splitOmega K (upperSplit K B u) (upperSplit K B v) = splitOmega K u v := by
  simp only [upperSplit_apply, splitOmega, add_dotProduct, dotProduct_add]
  rw [symmetric_dot]
  ring

@[simp] theorem splitOmega_lower (C : Symmetric3 K) (u v : Split K) :
    splitOmega K (lowerSplit K C u) (lowerSplit K C v) = splitOmega K u v := by
  simp only [lowerSplit_apply, splitOmega, add_dotProduct, dotProduct_add]
  rw [symmetric_dot]
  ring

@[simp] theorem splitOmega_scaledDiagonal (t : K) (u v : Split K) :
    splitOmega K (scaledDiagonalSplit K t u) (scaledDiagonalSplit K t v) =
      t^2 * splitOmega K u v := by
  simp [splitOmega, dotProduct, Fin.sum_univ_succ]
  ring

/-- The polynomial family is conformally symplectic with multiplier `t²`. -/
theorem omega_scaledGauss (t : K) (B C : Symmetric3 K) (u v : V K) :
    omega K (scaledGauss K t B C u) (scaledGauss K t B C v) = t^2 * omega K u v := by
  rw [omega_split, omega_split]
  change splitOmega K (splitV K (scaledGauss K t B C u))
    (splitV K (scaledGauss K t B C v)) = t^2 * splitOmega K (splitV K u) (splitV K v)
  rw [split_scaledGauss, split_scaledGauss, splitOmega_upper, splitOmega_scaledDiagonal,
    splitOmega_lower]

/-- A linear map preserving the actual symplectic form is automatically an actual equivalence. -/
def bundleSymplectic (f : V K →ₗ[K] V K)
    (hf : ∀ u v, omega K (f u) (f v) = omega K u v) : Sp6 K := by
  have hinj : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    apply bot_unique
    intro u hu
    change u = 0
    apply omega_separating_left K u
    intro v
    rw [← hf u v, show f u = 0 from hu]
    simp
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (K := K) (V := V K) (V₂ := V K) (f := f) rfl).mp hinj
  exact ⟨LinearEquiv.ofBijective f ⟨hinj,hsurj⟩,hf⟩

@[simp] theorem bundleSymplectic_apply (f : V K →ₗ[K] V K)
    (hf : ∀ u v, omega K (f u) (f v) = omega K u v) (v : V K) :
    (bundleSymplectic K f hf).val v = f v := rfl

/-- The actual Gauss symplectic transformation, defined whenever the torus parameter is nonzero. -/
def gauss (t : K) (ht : t ≠ 0) (B C : Symmetric3 K) : Sp6 K :=
  bundleSymplectic K (t⁻¹ • scaledGauss K t B C) (by
    intro u v
    simp only [LinearMap.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [omega_scaledGauss]
    field_simp [ht])

@[simp] theorem gauss_apply (t : K) (ht : t ≠ 0) (B C : Symmetric3 K) (v : V K) :
    (gauss K t ht B C).val v = t⁻¹ • scaledGauss K t B C v := rfl


/-- Literal polynomial entries of the scaled Gauss matrix, over any coefficient ring. -/
def gaussEntries {A : Type*} [CommRing A] (t : A)
    (B C : Matrix (Fin 3) (Fin 3) A) : Matrix (Fin 6) (Fin 6) A :=
  fun r c => Fin.addCases (m := 3) (n := 3)
    (fun i => Fin.addCases (m := 3) (n := 3)
      (fun j => (if i=j then ![t^2,t,t] i else 0) +
        ∑ k : Fin 3, B i k * (![1,t,t] k * C k j))
      (fun j => B i j * ![1,t,t] j) c)
    (fun i => Fin.addCases (m := 3) (n := 3) (fun j => ![1,t,t] i * C i j)
      (fun j => if i=j then ![1,t,t] i else 0) c) r

@[simp] theorem scaledGauss_e_e (t : K) (B C : Symmetric3 K) (i j : Fin 3) :
    scaledGauss K t B C (e K i) (eIndex j) =
      (if j=i then ![t^2,t,t] j else 0) +
        ∑ k : Fin 3, B.val j k * (![1,t,t] k * C.val k i) := by
  change (splitV K (scaledGauss K t B C (e K i))).1 j = _
  rw [split_scaledGauss]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, eq_comm]

@[simp] theorem scaledGauss_e_f (t : K) (B C : Symmetric3 K) (i j : Fin 3) :
    scaledGauss K t B C (e K i) (fIndex j) = ![1,t,t] j * C.val j i := by
  change (splitV K (scaledGauss K t B C (e K i))).2 j = _
  rw [split_scaledGauss]
  simp

@[simp] theorem scaledGauss_f_e (t : K) (B C : Symmetric3 K) (i j : Fin 3) :
    scaledGauss K t B C (f K i) (eIndex j) = B.val j i * ![1,t,t] i := by
  change (splitV K (scaledGauss K t B C (f K i))).1 j = _
  rw [split_scaledGauss]
  classical
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, eq_comm]

@[simp] theorem scaledGauss_f_f (t : K) (B C : Symmetric3 K) (i j : Fin 3) :
    scaledGauss K t B C (f K i) (fIndex j) = if j=i then ![1,t,t] j else 0 := by
  change (splitV K (scaledGauss K t B C (f K i))).2 j = _
  rw [split_scaledGauss]
  simp [Pi.single_apply, mul_ite, eq_comm]

/-- The explicit matrix is proved to be the actual scaled Gauss linear map. -/
theorem scaledGauss_entry (t : K) (B C : Symmetric3 K) (i j : Fin 6) :
    scaledGauss K t B C (basisVector K j) i = gaussEntries t B.val C.val i j := by
  refine Fin.addCases (m := 3) (n := 3) (motive := fun i : Fin 6 =>
    scaledGauss K t B C (basisVector K j) i = gaussEntries t B.val C.val i j) ?_ ?_ i
  · intro i
    refine Fin.addCases (m := 3) (n := 3) (motive := fun j : Fin 6 =>
      scaledGauss K t B C (basisVector K j) (i.castAdd 3) =
        gaussEntries t B.val C.val (i.castAdd 3) j) ?_ ?_ j
    · intro j
      simpa only [e, eIndex, gaussEntries, Fin.addCases_left, Fin.addCases_right] using scaledGauss_e_e K t B C j i
    · intro j
      simpa only [f, eIndex, fIndex, gaussEntries, Fin.addCases_left, Fin.addCases_right] using scaledGauss_f_e K t B C j i
  · intro i
    refine Fin.addCases (m := 3) (n := 3) (motive := fun j : Fin 6 =>
      scaledGauss K t B C (basisVector K j) (Fin.natAdd 3 i) =
        gaussEntries t B.val C.val (Fin.natAdd 3 i) j) ?_ ?_ j
    · intro j
      simpa only [e, eIndex, fIndex, gaussEntries, Fin.addCases_left, Fin.addCases_right] using scaledGauss_e_f K t B C j i
    · intro j
      simpa only [f, fIndex, gaussEntries, Fin.addCases_left, Fin.addCases_right] using scaledGauss_f_f K t B C j i

abbrev ParameterRing := MvPolynomial (Fin 13) K

def upperParameters {A : Type*} (z : Fin 13 → A) : Matrix (Fin 3) (Fin 3) A :=
  ![![z 1,z 2,z 3], ![z 2,z 4,z 5], ![z 3,z 5,z 6]]
def lowerParameters {A : Type*} (z : Fin 13 → A) : Matrix (Fin 3) (Fin 3) A :=
  ![![z 7,z 8,z 9], ![z 8,z 10,z 11], ![z 9,z 11,z 12]]

theorem upperParameters_symmetric {A : Type*} (z : Fin 13 → A) :
    (upperParameters z).transpose = upperParameters z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem lowerParameters_symmetric {A : Type*} (z : Fin 13 → A) :
    (lowerParameters z).transpose = lowerParameters z := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

def upperParameterMatrix (z : Fin 13 → K) : Symmetric3 K :=
  ⟨upperParameters z,upperParameters_symmetric z⟩
def lowerParameterMatrix (z : Fin 13 → K) : Symmetric3 K :=
  ⟨lowerParameters z,lowerParameters_symmetric z⟩

/-- Actual formal polynomial matrix of the thirteen-parameter family. -/
def formalMatrix : Matrix (Fin 6) (Fin 6) (ParameterRing K) :=
  gaussEntries (MvPolynomial.X 0) (upperParameters MvPolynomial.X)
    (lowerParameters MvPolynomial.X)

/-- The actual exterior-coordinate minor of `map3 H (a+b)`. -/
def minorSum {A : Type*} [CommRing A] (H : Matrix (Fin 6) (Fin 6) A) (i j k : Fin 6) : A :=
  Matrix.det (fun r c : Fin 3 => H (![i,j,k] c) (eIndex r)) +
    Matrix.det (fun r c : Fin 3 => H (![i,j,k] c) (fIndex r))

def formalA : ParameterRing K := minorSum (formalMatrix K) 0 1 2

def formalTarget : Fin 13 → ParameterRing K :=
  ![minorSum (formalMatrix K) 3 4 5,
    minorSum (formalMatrix K) 0 4 5, minorSum (formalMatrix K) 0 5 3,
    minorSum (formalMatrix K) 0 3 4, minorSum (formalMatrix K) 1 5 3,
    minorSum (formalMatrix K) 1 3 4, minorSum (formalMatrix K) 2 3 4,
    minorSum (formalMatrix K) 3 1 2, minorSum (formalMatrix K) 3 2 0,
    minorSum (formalMatrix K) 3 0 1, minorSum (formalMatrix K) 4 2 0,
    minorSum (formalMatrix K) 4 0 1, minorSum (formalMatrix K) 5 0 1]

/-- The actual identity point `t=1, B=C=0`. -/
def basePoint : Fin 13 → K := Pi.single 0 1

def evalBase : ParameterRing K →+* K := MvPolynomial.eval (basePoint K)


/-- Ring homomorphisms preserve the literal entries of the Gauss family. -/
theorem map_gaussEntries {A D : Type*} [CommRing A] [CommRing D] (φ : A →+* D)
    (t : A) (B C : Matrix (Fin 3) (Fin 3) A) (i j : Fin 6) :
    φ (gaussEntries t B C i j) = gaussEntries (φ t) (B.map φ) (C.map φ) i j := by
  have hE (i : Fin 3) : φ (![t^2,t,t] i) = ![φ t^2,φ t,φ t] i := by
    fin_cases i <;> simp
  have hF (i : Fin 3) : φ (![1,t,t] i) = ![1,φ t,φ t] i := by
    fin_cases i <;> simp
  simp only [gaussEntries, Fin.addCases]
  split_ifs <;> simp [hE,hF]

/-- Ring homomorphisms preserve the actual exterior-coordinate minors. -/
theorem map_minorSum {A D : Type*} [CommRing A] [CommRing D] (φ : A →+* D)
    (H : Matrix (Fin 6) (Fin 6) A) (i j k : Fin 6) :
    φ (minorSum H i j k) = minorSum (H.map φ) i j k := by
  simp only [minorSum, map_add, RingHom.map_det]
  rfl

theorem eval_formalMatrix (z : Fin 13 → K) :
    (formalMatrix K).map (MvPolynomial.eval z) =
      gaussEntries (z 0) (upperParameters z) (lowerParameters z) := by
  have hB : (upperParameters (MvPolynomial.X : Fin 13 → ParameterRing K)).map
      (MvPolynomial.eval z) = upperParameters z := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [upperParameters]
  have hC : (lowerParameters (MvPolynomial.X : Fin 13 → ParameterRing K)).map
      (MvPolynomial.eval z) = lowerParameters z := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerParameters]
  ext i j
  simp only [formalMatrix, Matrix.map_apply, map_gaussEntries, MvPolynomial.eval_X, hB, hC]

@[simp] theorem evalBase_formalMatrix : (formalMatrix K).map (evalBase K) = 1 := by
  rw [evalBase, eval_formalMatrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gaussEntries,basePoint,upperParameters,lowerParameters,Fin.addCases,
      Pi.single_apply,Fin.sum_univ_succ]

@[simp] theorem evalBase_formalA : evalBase K (formalA K) = 1 := by
  rw [formalA, map_minorSum, evalBase_formalMatrix]
  norm_num [minorSum,Matrix.det_fin_three,eIndex,fIndex,Matrix.one_apply]

@[simp] theorem evalBase_formalTarget (i : Fin 13) :
    evalBase K (formalTarget K i) = if i=0 then 1 else 0 := by
  fin_cases i <;> simp only [formalTarget,Matrix.cons_val_zero',Matrix.cons_val_succ'] <;>
    rw [map_minorSum, evalBase_formalMatrix] <;>
    norm_num [minorSum,Matrix.det_fin_three,eIndex,fIndex,Matrix.one_apply]


/-- The formal minors are actual exterior coordinates of the transformed split vector. -/
theorem coordinate_map_split (F : V K →ₗ[K] V K) (i j k : Fin 6) :
    coordinate K i j k (exteriorPower.map 3 F (a K + b K)) =
      minorSum (fun r c => F (basisVector K c) r) i j k := by
  simp [minorSum,a,b,wedge3,coordinate,exteriorPower.map_apply_ιMulti,
    Matrix.det_fin_three,e,f]

theorem eval_minor_formalMatrix (z : Fin 13 → K) (i j k : Fin 6) :
    MvPolynomial.eval z (minorSum (formalMatrix K) i j k) =
      coordinate K i j k (exteriorPower.map 3
        (scaledGauss K (z 0) (upperParameterMatrix K z) (lowerParameterMatrix K z)) (a K+b K)) := by
  rw [map_minorSum, eval_formalMatrix, coordinate_map_split]
  congr 1
  funext r c
  exact (scaledGauss_entry K (z 0) (upperParameterMatrix K z)
    (lowerParameterMatrix K z) r c).symm

set_option maxHeartbeats 3000000 in
@[simp] theorem evalBase_pderiv_formalA (j : Fin 13) :
    evalBase K (MvPolynomial.pderiv j (formalA K)) = if j=0 then 4 else 0 := by
  fin_cases j <;> unfold formalA minorSum <;>
    simp only [Matrix.det_fin_three] <;>
    norm_num [evalBase,basePoint,formalMatrix,gaussEntries,upperParameters,lowerParameters,
      MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,MvPolynomial.pderiv_one,
      Fin.sum_univ_succ,Fin.addCases,eIndex,fIndex,Pi.single_apply]

set_option maxHeartbeats 8000000 in
@[simp] theorem evalBase_pderiv_formalTarget (i j : Fin 13) :
    evalBase K (MvPolynomial.pderiv j (formalTarget K i)) =
      if i=0 then (if j=0 then 2 else 0) else (if i=j then 1 else 0) := by
  fin_cases i <;> simp only [formalTarget,Matrix.cons_val_zero',Matrix.cons_val_succ'] <;>
    unfold minorSum <;> simp only [Matrix.det_fin_three] <;>
    norm_num [evalBase,basePoint,formalMatrix,gaussEntries,upperParameters,lowerParameters,
      MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,MvPolynomial.pderiv_one,
      Fin.sum_univ_succ,Fin.addCases,eIndex,fIndex,Pi.single_apply,mul_ite,ite_mul]
  all_goals fin_cases j <;> norm_num [Pi.single_apply]

/-- Numerator of the Jacobian of the actual chart map `N_i/A`. -/
def chartJacobian : Matrix (Fin 13) (Fin 13) (ParameterRing K) :=
  fun i j => formalA K * MvPolynomial.pderiv j (formalTarget K i) -
    formalTarget K i * MvPolynomial.pderiv j (formalA K)

/-- The thirteen tangent directions give the exact diagonal `(-2,1,...,1)`. -/
theorem evalBase_chartJacobian :
    (chartJacobian K).map (evalBase K) = Matrix.diagonal (fun i : Fin 13 => if i=0 then -2 else 1) := by
  ext i j
  simp only [chartJacobian,Matrix.map_apply,map_sub,map_mul,evalBase_formalA,
    evalBase_formalTarget,evalBase_pderiv_formalA,evalBase_pderiv_formalTarget,one_mul,
    Matrix.diagonal_apply]
  by_cases hi : i=0 <;> by_cases hj : j=0 <;> by_cases hij : i=j
  all_goals simp_all
  all_goals norm_num

/-- An actual nonzero Jacobian determinant at the split point. -/
theorem evalBase_chartJacobian_det : evalBase K (Matrix.det (chartJacobian K)) = -2 := by
  rw [RingHom.map_det]
  change Matrix.det ((chartJacobian K).map (evalBase K)) = -2
  rw [evalBase_chartJacobian,Matrix.det_diagonal]
  norm_num [Fin.prod_univ_succ]

theorem chartJacobian_det_ne_zero [CharZero K] : Matrix.det (chartJacobian K) ≠ 0 := by
  intro hz
  have h := congrArg (evalBase K) hz
  rw [evalBase_chartJacobian_det,map_zero] at h
  norm_num at h

/-- Scalar multiplication of an actual linear map acts cubically on its third exterior power. -/
theorem exterior_map_smul (c : K) (F : V K →ₗ[K] V K) :
    exteriorPower.map 3 (c • F) = c^3 • exteriorPower.map 3 F := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply,exteriorPower.map_apply_ιMulti,LinearMap.smul_apply]
  change exteriorPower.ιMulti K 3 (fun i => c • F (v i)) =
    c^3 • exteriorPower.ιMulti K 3 (fun i => F (v i))
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
    (exteriorPower.ιMulti K 3).map_smul_univ (fun _ : Fin 3 => c) (fun i => F (v i))

theorem scaledGauss_eq_smul_gauss (t : K) (ht : t ≠ 0) (B C : Symmetric3 K) :
    scaledGauss K t B C = t • (gauss K t ht B C).val.toLinearMap := by
  apply LinearMap.ext
  intro v
  change scaledGauss K t B C v = t • (gauss K t ht B C).val v
  rw [gauss_apply,smul_smul,mul_inv_cancel₀ ht,one_smul]

/-- The denominator-free polynomial family lies in the actual projective symplectic orbit. -/
theorem scaledGauss_orbit (t : K) (ht : t ≠ 0) (B C : Symmetric3 K) :
    exteriorPower.map 3 (scaledGauss K t B C) (a K+b K) =
      t^3 • exteriorAction K (gauss K t ht B C) (a K+b K) := by
  rw [scaledGauss_eq_smul_gauss K t ht B C,exterior_map_smul]
  rfl


/-- The thirteen remaining actual exterior coefficients on the `a≠0` chart. -/
def coordinateFunctionals : Fin 13 → (Third K →ₗ[K] K) :=
  ![bCoordinate K,
    qCoordinate K 0 0,qCoordinate K 0 1,qCoordinate K 0 2,
    qCoordinate K 1 1,qCoordinate K 1 2,qCoordinate K 2 2,
    pCoordinate K 0 0,pCoordinate K 0 1,pCoordinate K 0 2,
    pCoordinate K 1 1,pCoordinate K 1 2,pCoordinate K 2 2]

def coordinateTuple : Third K →ₗ[K] (Fin 13 → K) := LinearMap.pi (coordinateFunctionals K)

/-- The full minor vector is proved to be the actual exterior coordinate vector. -/
theorem eval_formalTarget_tuple (z : Fin 13 → K) :
    (fun i => MvPolynomial.eval z (formalTarget K i)) =
      coordinateTuple K (exteriorPower.map 3
        (scaledGauss K (z 0) (upperParameterMatrix K z) (lowerParameterMatrix K z)) (a K+b K)) := by
  funext i
  fin_cases i <;>
    simp only [formalTarget,coordinateTuple,LinearMap.pi_apply,coordinateFunctionals,
      Matrix.cons_val_zero',Matrix.cons_val_succ']
  all_goals exact eval_minor_formalMatrix K z _ _ _

@[simp] theorem coordinateTuple_embedding (r : PrimitiveRepresentation.Coordinates K) :
    coordinateTuple K (coordinateEmbedding K r) =
      ![r.2.2.2,r.2.1.val 0 0,r.2.1.val 0 1,r.2.1.val 0 2,
        r.2.1.val 1 1,r.2.1.val 1 2,r.2.1.val 2 2,
        r.2.2.1.val 0 0,r.2.2.1.val 0 1,r.2.2.1.val 0 2,
        r.2.2.1.val 1 1,r.2.2.1.val 1 2,r.2.2.1.val 2 2] := by
  funext i
  fin_cases i <;> simp [coordinateTuple,coordinateFunctionals]

/-- Actual affine coordinates of the normalized primitive chart. -/
def chartCoordinates (y : Fin 13 → K) : PrimitiveRepresentation.Coordinates K :=
  (1,upperParameterMatrix K y,lowerParameterMatrix K y,y 0)

def chartVector [CharZero K] (y : Fin 13 → K) : Primitive K :=
  primitiveEquiv K (chartCoordinates K y)

@[simp] theorem aCoordinate_chartVector [CharZero K] (y : Fin 13 → K) :
    aCoordinate K (chartVector K y).val = 1 := by simp [chartVector,chartCoordinates]

@[simp] theorem coordinateTuple_chartVector [CharZero K] (y : Fin 13 → K) :
    coordinateTuple K (chartVector K y).val = y := by
  change coordinateTuple K (coordinateEmbedding K (chartCoordinates K y)) = y
  rw [coordinateTuple_embedding]
  funext i
  fin_cases i <;> rfl

/-- Scalar coefficient and the thirteen chart entries determine an actual primitive vector. -/
theorem primitive_ext_tuple [CharZero K] (u v : Primitive K)
    (ha : aCoordinate K u.val = aCoordinate K v.val)
    (h : coordinateTuple K u.val = coordinateTuple K v.val) : u = v := by
  have hc (i : Fin 13) : coordinateFunctionals K i u.val = coordinateFunctionals K i v.val :=
    congrFun h i
  apply primitive_ext_upper K u v ha (hc 0)
  · rintro ⟨⟨i,j⟩,hij⟩
    fin_cases i <;> fin_cases j <;> norm_num at hij
    all_goals first | exact hc 1 | exact hc 2 | exact hc 3 | exact hc 4 | exact hc 5 | exact hc 6
  · rintro ⟨⟨i,j⟩,hij⟩
    fin_cases i <;> fin_cases j <;> norm_num at hij
    all_goals first | exact hc 7 | exact hc 8 | exact hc 9 | exact hc 10 | exact hc 11 | exact hc 12

/-- The actual primitive vector furnished by the Gauss transformation. -/
def familyPrimitive (z : Fin 13 → K) (ht : z 0 ≠ 0) : Primitive K :=
  (z 0)^3 • primitiveAction K
    (gauss K (z 0) ht (upperParameterMatrix K z) (lowerParameterMatrix K z)) (rho K)

@[simp] theorem familyPrimitive_val (z : Fin 13 → K) (ht : z 0 ≠ 0) :
    (familyPrimitive K z ht).val = exteriorPower.map 3
      (scaledGauss K (z 0) (upperParameterMatrix K z) (lowerParameterMatrix K z)) (a K+b K) := by
  change (z 0)^3 • exteriorAction K
    (gauss K (z 0) ht (upperParameterMatrix K z) (lowerParameterMatrix K z)) (a K+b K) = _
  exact (scaledGauss_orbit K (z 0) ht (upperParameterMatrix K z) (lowerParameterMatrix K z)).symm

@[simp] theorem familyPrimitive_a (z : Fin 13 → K) (ht : z 0 ≠ 0) :
    aCoordinate K (familyPrimitive K z ht).val = MvPolynomial.eval z (formalA K) := by
  rw [familyPrimitive_val]
  exact (eval_minor_formalMatrix K z 0 1 2).symm

@[simp] theorem familyPrimitive_tuple (z : Fin 13 → K) (ht : z 0 ≠ 0) :
    coordinateTuple K (familyPrimitive K z ht).val = fun i => MvPolynomial.eval z (formalTarget K i) := by
  rw [familyPrimitive_val]
  exact (eval_formalTarget_tuple K z).symm

/-- The literal rational chart map whose Jacobian was computed above. -/
def chartPoint (z : Fin 13 → K) : Fin 13 → K :=
  fun i => MvPolynomial.eval z (formalTarget K i) / MvPolynomial.eval z (formalA K)

theorem chartVector_chartPoint [CharZero K] (z : Fin 13 → K) (ht : z 0 ≠ 0)
    (hA : MvPolynomial.eval z (formalA K) ≠ 0) :
    chartVector K (chartPoint K z) = (MvPolynomial.eval z (formalA K))⁻¹ • familyPrimitive K z ht := by
  apply primitive_ext_tuple K
  · simp only [aCoordinate_chartVector,Submodule.coe_smul,map_smul,familyPrimitive_a,
      smul_eq_mul,inv_mul_cancel₀ hA]
  · rw [coordinateTuple_chartVector]
    simp only [Submodule.coe_smul,map_smul,familyPrimitive_tuple]
    funext i
    simp only [chartPoint,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv]
    exact mul_comm _ _

/-- Every point of this literal rational family is proved to be in the actual projective orbit. -/
theorem chartPoint_in_orbit [CharZero K] (z : Fin 13 → K) (ht : z 0 ≠ 0)
    (hA : MvPolynomial.eval z (formalA K) ≠ 0) :
    ∃ (h : Sp6 K) (c : K), c ≠ 0 ∧
      chartVector K (chartPoint K z) = c • primitiveAction K h (rho K) := by
  refine ⟨gauss K (z 0) ht (upperParameterMatrix K z) (lowerParameterMatrix K z),
    (MvPolynomial.eval z (formalA K))⁻¹ * (z 0)^3,
    mul_ne_zero (inv_ne_zero hA) (pow_ne_zero 3 ht), ?_⟩
  rw [chartVector_chartPoint K z ht hA]
  exact smul_smul _ _ _

end M9.PrimitiveOpenOrbit
