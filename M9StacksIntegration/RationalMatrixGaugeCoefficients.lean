module

public import M9StacksIntegration.RationalMatrixGauge
public import M9.FiniteNoNameField

/-!
# Coefficient-action naturality of actual rational matrix gauges

The action on polynomial and fraction fields is the original coefficient
action from `FiniteNoNameField`.  Matrix substitution commutes with that
action when the two invertible coefficient matrices are translated too.
The group may be infinite.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MvPolynomial Matrix
open M9.FiniteNoNameField

namespace M9Native.RationalMatrixGaugeCoefficients

open RationalMatrixGauge

variable (G K : Type*) [Group G] [Field K] [MulSemiringAction G K]
variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The actual coefficient map of the fixed original polynomial action. -/
def coefficientMap (g : G) : P K n →+* P K n :=
  MvPolynomial.map (MulSemiringAction.toRingHom G K g)

omit [Fintype n] [DecidableEq n] in
theorem coefficientMap_X (g : G) (ij : n × n) :
    coefficientMap G K n g (X ij) = X ij :=
  MvPolynomial.map_X (MulSemiringAction.toRingHom G K g) ij

omit [Fintype n] [DecidableEq n] in
theorem coefficientMap_C (g : G) (c : K) :
    coefficientMap G K n g (C c) = C (g • c) :=
  MvPolynomial.map_C (MulSemiringAction.toRingHom G K g) c

/-- Coefficient translation preserves the original invertible matrices. -/
def coefficientUnit (g : G) (L : MatrixUnit K n) : MatrixUnit K n :=
  Units.map ((MulSemiringAction.toRingHom G K g).mapMatrix (m := n)).toMonoidHom L

theorem coefficientUnit_val (g : G) (L : MatrixUnit K n) :
    (coefficientUnit G K n g L).val =
      L.val.map (MulSemiringAction.toRingHom G K g) := rfl

theorem coefficientMap_polynomialMatrix (g : G) :
    (polynomialMatrix K n).map (coefficientMap G K n g) = polynomialMatrix K n := by
  apply Matrix.ext
  intro i j
  exact coefficientMap_X G K n g (i,j)

theorem coefficientMap_constantMatrix (g : G) (L : MatrixUnit K n) :
    (constantMatrix K n L).map (coefficientMap G K n g) =
      constantMatrix K n (coefficientUnit G K n g L) := by
  apply Matrix.ext
  intro i j
  change coefficientMap G K n g (C (L.val i j)) = C (g • L.val i j)
  exact coefficientMap_C G K n g (L.val i j)

/-- The actual polynomial coefficient map commutes with matrix substitution. -/
theorem coefficientMap_gaugeHom (g : G) (L R : MatrixUnit K n) (p : P K n) :
    coefficientMap G K n g (gaugeHom K n L R p) =
      gaugeHom K n (coefficientUnit G K n g L) (coefficientUnit G K n g R)
        (coefficientMap G K n g p) := by
  have h : (coefficientMap G K n g).comp (gaugeHom K n L R).toRingHom =
      (gaugeHom K n (coefficientUnit G K n g L)
        (coefficientUnit G K n g R)).toRingHom.comp (coefficientMap G K n g) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change coefficientMap G K n g (gaugeHom K n L R (C c)) =
        gaugeHom K n (coefficientUnit G K n g L) (coefficientUnit G K n g R)
          (coefficientMap G K n g (C c))
      have hc : gaugeHom K n L R (C c) = C c := (gaugeHom K n L R).commutes c
      rw [hc, coefficientMap_C]
      exact ((gaugeHom K n (coefficientUnit G K n g L)
        (coefficientUnit G K n g R)).commutes (g • c)).symm
    · intro ij
      change coefficientMap G K n g (gaugeHom K n L R (X ij)) = _
      rw [show gaugeHom K n L R (X ij) =
        (constantMatrix K n L * polynomialMatrix K n * constantMatrix K n R) ij.1 ij.2
        from polynomialEquiv_variable K n L R ij.1 ij.2]
      change ((constantMatrix K n L * polynomialMatrix K n * constantMatrix K n R).map
        (coefficientMap G K n g)) ij.1 ij.2 = _
      rw [Matrix.map_mul, Matrix.map_mul, coefficientMap_constantMatrix,
        coefficientMap_polynomialMatrix, coefficientMap_constantMatrix]
      change _ = gaugeHom K n (coefficientUnit G K n g L)
        (coefficientUnit G K n g R) (coefficientMap G K n g (X ij))
      rw [coefficientMap_X]
      exact (polynomialEquiv_variable K n (coefficientUnit G K n g L)
        (coefficientUnit G K n g R) ij.1 ij.2).symm
  exact RingHom.congr_fun h p

theorem polynomialEquiv_coefficient_action (g : G) (L R : MatrixUnit K n) (p : P K n) :
    g • polynomialEquiv K n L R p =
      polynomialEquiv K n (coefficientUnit G K n g L) (coefficientUnit G K n g R)
        (g • p) :=
  coefficientMap_gaugeHom G K n g L R p

theorem fieldEquiv_polynomial (L R : MatrixUnit K n) (p : P K n) :
    fieldEquiv K n L R (algebraMap (P K n) (F K n) p) =
      algebraMap (P K n) (F K n) (polynomialEquiv K n L R p) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap _ _

/-- The same identity holds on the actual fraction field, with the
canonical coefficient action and no finiteness assumption on the group. -/
theorem fieldEquiv_coefficient_action (g : G) (L R : MatrixUnit K n) (f : F K n) :
    g • fieldEquiv K n L R f =
      fieldEquiv K n (coefficientUnit G K n g L) (coefficientUnit G K n g R) (g • f) := by
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective (P K n) f
  simp only [map_div₀, smul_div₀', fieldEquiv_polynomial, rationalAction_polynomial,
    polynomialEquiv_coefficient_action]

end M9Native.RationalMatrixGaugeCoefficients
