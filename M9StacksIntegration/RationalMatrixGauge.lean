module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-! Actual left-right matrix changes of independent rational coordinates.
Both inverses are constructed by polynomial substitution before passing to
fraction fields. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

open MvPolynomial Matrix
open scoped Classical

namespace M9Native.RationalMatrixGauge

variable (K : Type*) [Field K]
variable (n : Type*) [Fintype n] [DecidableEq n]

abbrev P (K n : Type*) [CommSemiring K] := MvPolynomial (n × n) K
abbrev F (K n : Type*) [Field K] := FractionRing (P K n)
abbrev MatrixUnit (K n : Type*) [Semiring K] [Fintype n] [DecidableEq n] :=
  Matrix.GeneralLinearGroup n K

def polynomialMatrix (K n : Type*) [Field K] [Fintype n] [DecidableEq n] : Matrix n n (P K n) := fun i j => X (i,j)

def constantMatrix (g : MatrixUnit K n) : Matrix n n (P K n) := g.val.map C

def gaugeHom (L R : MatrixUnit K n) : P K n →ₐ[K] P K n :=
  aeval (fun ij => (constantMatrix K n L * polynomialMatrix K n * constantMatrix K n R) ij.1 ij.2)

theorem gaugeHom_matrix (L R : MatrixUnit K n) :
    (polynomialMatrix K n).map (gaugeHom K n L R).toRingHom =
      constantMatrix K n L * polynomialMatrix K n * constantMatrix K n R := by
  apply Matrix.ext
  intro i j
  exact aeval_X _ _

theorem gaugeHom_constant (L R g : MatrixUnit K n) :
    (constantMatrix K n g).map (gaugeHom K n L R).toRingHom = constantMatrix K n g := by
  apply Matrix.ext
  intro i j
  exact (gaugeHom K n L R).commutes (g.val i j)

theorem constantMatrix_mul (g h : MatrixUnit K n) :
    constantMatrix K n (g*h) = constantMatrix K n g * constantMatrix K n h := by
  exact Matrix.map_mul

theorem constantMatrix_one : constantMatrix K n (1 : MatrixUnit K n) = 1 := by
  change (1 : Matrix n n K).map (MvPolynomial.C : K →+* P K n) = 1
  exact Matrix.map_one (n := n) (MvPolynomial.C : K →+* P K n)
    (map_zero _) (map_one _)

theorem gaugeHom_inverse (L R : MatrixUnit K n) :
    (gaugeHom K n L R).comp (gaugeHom K n L⁻¹ R⁻¹) = AlgHom.id K (P K n) := by
  apply MvPolynomial.algHom_ext
  intro ij
  have h := congrFun (congrFun
    (show ((constantMatrix K n L⁻¹ * polynomialMatrix K n * constantMatrix K n R⁻¹).map
      (gaugeHom K n L R).toRingHom) = polynomialMatrix K n from by
        rw [Matrix.map_mul, Matrix.map_mul, gaugeHom_constant, gaugeHom_constant,
          gaugeHom_matrix]
        calc
          constantMatrix K n L⁻¹ *
              (constantMatrix K n L * polynomialMatrix K n * constantMatrix K n R) *
              constantMatrix K n R⁻¹ =
              (constantMatrix K n L⁻¹ * constantMatrix K n L) * polynomialMatrix K n *
                (constantMatrix K n R * constantMatrix K n R⁻¹) := by
            simp only [Matrix.mul_assoc]
          _ = _ := by
            rw [← constantMatrix_mul, inv_mul_cancel, constantMatrix_one, Matrix.one_mul,
              ← constantMatrix_mul, mul_inv_cancel, constantMatrix_one, Matrix.mul_one]) ij.1) ij.2
  change gaugeHom K n L R (gaugeHom K n L⁻¹ R⁻¹ (X ij)) = X ij
  rw [show gaugeHom K n L⁻¹ R⁻¹ (X ij) =
      (constantMatrix K n L⁻¹ * polynomialMatrix K n * constantMatrix K n R⁻¹) ij.1 ij.2
    from aeval_X _ _]
  exact h

/-- A genuine polynomial automorphism with the inverse substitution proved. -/
def polynomialEquiv (L R : MatrixUnit K n) : P K n ≃ₐ[K] P K n :=
  AlgEquiv.ofAlgHom (gaugeHom K n L R) (gaugeHom K n L⁻¹ R⁻¹)
    (gaugeHom_inverse K n L R)
    (by simpa only [inv_inv] using gaugeHom_inverse K n L⁻¹ R⁻¹)

def fieldEquiv (L R : MatrixUnit K n) : F K n ≃ₐ[K] F K n :=
  IsFractionRing.algEquivOfAlgEquiv (polynomialEquiv K n L R)

theorem polynomialEquiv_variable (L R : MatrixUnit K n) (i j : n) :
    polynomialEquiv K n L R (polynomialMatrix K n i j) =
      (constantMatrix K n L * polynomialMatrix K n * constantMatrix K n R) i j := by
  exact aeval_X _ _

def rationalMatrix (K n : Type*) [Field K] [Fintype n] [DecidableEq n] : Matrix n n (F K n) :=
  (polynomialMatrix K n).map (algebraMap (P K n) (F K n))

theorem fieldEquiv_variable (L R : MatrixUnit K n) (i j : n) :
    fieldEquiv K n L R (rationalMatrix K n i j) =
      (L.val.map (algebraMap K (F K n)) * rationalMatrix K n *
        R.val.map (algebraMap K (F K n))) i j := by
  rw [rationalMatrix, Matrix.map_apply, fieldEquiv,
    IsFractionRing.algEquivOfAlgEquiv_algebraMap, polynomialEquiv_variable]
  change algebraMap (P K n) (F K n)
    ((constantMatrix K n L * polynomialMatrix K n * constantMatrix K n R) i j) = _
  change ((constantMatrix K n L * polynomialMatrix K n * constantMatrix K n R).map
    (algebraMap (P K n) (F K n))) i j = _
  rw [Matrix.map_mul, Matrix.map_mul]
  have hL : (constantMatrix K n L).map (algebraMap (P K n) (F K n)) =
      L.val.map (algebraMap K (F K n)) := by
    apply Matrix.ext
    intro a b
    exact (IsScalarTower.algebraMap_apply K (P K n) (F K n) (L.val a b)).symm
  have hR : (constantMatrix K n R).map (algebraMap (P K n) (F K n)) =
      R.val.map (algebraMap K (F K n)) := by
    apply Matrix.ext
    intro a b
    exact (IsScalarTower.algebraMap_apply K (P K n) (F K n) (R.val a b)).symm
  rw [hL,hR]

theorem fieldEquiv_matrix (L R : MatrixUnit K n) :
    (rationalMatrix K n).map (fieldEquiv K n L R).toRingHom =
      L.val.map (algebraMap K (F K n)) * rationalMatrix K n *
        R.val.map (algebraMap K (F K n)) := by
  apply Matrix.ext
  intro i j
  exact fieldEquiv_variable K n L R i j

end M9Native.RationalMatrixGauge
