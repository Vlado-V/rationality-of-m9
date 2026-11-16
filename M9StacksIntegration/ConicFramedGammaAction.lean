module

public import M9StacksIntegration.ConicFramedGraphField
public import M9.CayleyField

/-! The literal raw-Hom generator formula for the genuine induced deck
action. The matrix γ is the actual scalar extension of the original E₀
representation. No equality of field actions is assumed. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

open Matrix
open scoped Classical

namespace M9Native.ConicFramedGammaAction

open M9.GraphBundleDescent ConicPairMovingFrames ConicFramedGraphField
open ConicRawGammaMatrices

def coefficientUnit : GL4 B →* GL4 M := Matrix.GeneralLinearGroup.map (algebraMap B M)
def beta (s : Fin 2) : GL4 M := coefficientUnit (compensatedFrame s)

def rawUnit : GL4 M := Matrix.GeneralLinearGroup.mkOfDetNeZero genericRawMatrix
  (show genericRawMatrix.det ≠ 0 from M9.CayleyField.genericMatrix_det_ne_zero B)

def gaugedUnit : GL4 M := beta 1 * rawUnit * (beta 0)⁻¹

theorem induced_constant (g : G) (b : B) :
    inducedRepresentation g (algebraMap B M b) =
      algebraMap B M (ConicGraphCoefficientDescent.frameRepresentation g b) := by
  calc
    _ = inducedRepresentation g (movingGauge (algebraMap B M b)) :=
      congrArg (inducedRepresentation g) (movingGauge_constant b).symm
    _ = movingGauge (coefficientEquiv g (algebraMap B M b)) := inducedRepresentation_gauge g _
    _ = movingGauge (algebraMap B M (ConicGraphCoefficientDescent.frameRepresentation g b)) :=
      congrArg movingGauge (coefficientEquiv_constant g b)
    _ = _ := movingGauge_constant _

theorem induced_coefficientUnit (g : G) (U : GL4 B) :
    Matrix.GeneralLinearGroup.map (inducedRepresentation g).toRingHom (coefficientUnit U) =
      coefficientUnit
        (Matrix.GeneralLinearGroup.map (ConicGraphCoefficientDescent.frameRepresentation g).toRingHom U) := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact induced_constant g (U.val i j)

theorem induced_beta (g : G) (s : Fin 2) :
    Matrix.GeneralLinearGroup.map (inducedRepresentation g).toRingHom (beta s) =
      beta s * gammaK M (![g.1,g.2] s) := by
  calc
    _ = coefficientUnit
        (Matrix.GeneralLinearGroup.map (ConicGraphCoefficientDescent.frameRepresentation g).toRingHom
          (compensatedFrame s)) := induced_coefficientUnit g _
    _ = coefficientUnit (compensatedFrame s * gammaK B (![g.1,g.2] s)) :=
      congrArg coefficientUnit (ConicPairCompensatorAction.compensatedFrame_action g s)
    _ = beta s * coefficientUnit (gammaK B (![g.1,g.2] s)) := coefficientUnit.map_mul _ _
    _ = _ := congrArg (fun u => beta s * u)
      (map_gammaK B (IsScalarTower.toAlgHom ℂ B M) (![g.1,g.2] s))

theorem gaugedUnit_entry (i j : Fin 4) :
    gaugedUnit.val i j = movingGauge (genericRawMatrix i j) := by
  have h := RationalMatrixGauge.fieldEquiv_variable B (Fin 4) (compensatedFrame 1)
    (compensatedFrame 0)⁻¹ i j
  change movingGauge (genericRawMatrix i j) =
    ((coefficientUnit (compensatedFrame 1)).val * rawUnit.val *
      (coefficientUnit ((compensatedFrame 0)⁻¹)).val) i j at h
  have hi := coefficientUnit.map_inv (compensatedFrame 0)
  exact (congrArg (fun U : GL4 M => (beta 1 * rawUnit * U).val i j) hi).symm.trans h.symm

/-- The actual moving tensor-fibre coordinates are fixed by the deck action. -/
theorem induced_gaugedUnit (g : G) :
    Matrix.GeneralLinearGroup.map (inducedRepresentation g).toRingHom gaugedUnit = gaugedUnit := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  calc
    inducedRepresentation g (gaugedUnit.val i j) =
        inducedRepresentation g (movingGauge (genericRawMatrix i j)) :=
      congrArg (inducedRepresentation g) (gaugedUnit_entry i j)
    _ = movingGauge (coefficientEquiv g (genericRawMatrix i j)) := inducedRepresentation_gauge g _
    _ = movingGauge (genericRawMatrix i j) :=
      congrArg movingGauge (coefficientEquiv_variable g (i,j))
    _ = _ := (gaugedUnit_entry i j).symm

/-- The induced field action on the actual generic raw isomorphism is the
original inverse-left/right tensor action. -/
theorem induced_rawUnit (g : G) :
    Matrix.GeneralLinearGroup.map (inducedRepresentation g).toRingHom rawUnit =
      (gammaK M g.2)⁻¹ * rawUnit * gammaK M g.1 := by
  let σ : GL4 M →* GL4 M := Matrix.GeneralLinearGroup.map (inducedRepresentation g).toRingHom
  let A := beta 1
  let C := beta 0
  let a := gammaK M g.1
  let b := gammaK M g.2
  have h : (A*b) * σ rawUnit * (C*a)⁻¹ = A * rawUnit * C⁻¹ := by
    have ht := induced_gaugedUnit g
    change σ (beta 1 * rawUnit * (beta 0)⁻¹) = beta 1 * rawUnit * (beta 0)⁻¹ at ht
    rw [map_mul, map_mul, map_inv, induced_beta, induced_beta] at ht
    exact ht
  calc
    σ rawUnit = (A*b)⁻¹ * ((A*b) * σ rawUnit * (C*a)⁻¹) * (C*a) := by group
    _ = (A*b)⁻¹ * (A * rawUnit * C⁻¹) * (C*a) :=
      congrArg (fun z => (A*b)⁻¹ * z * (C*a)) h
    _ = b⁻¹ * rawUnit * a := by group

/-- Literal generator formula in the original sixteen independent raw
coordinates, derived from the actual compensator identities. -/
theorem induced_rawMatrix (g : G) :
    genericRawMatrix.map (inducedRepresentation g).toRingHom =
      (gammaK M g.2)⁻¹.val * genericRawMatrix * (gammaK M g.1).val :=
  congrArg Units.val (induced_rawUnit g)

theorem induced_variable (g : G) (i j : Fin 4) :
    inducedRepresentation g (genericRawMatrix i j) =
      ((gammaK M g.2)⁻¹.val * genericRawMatrix * (gammaK M g.1).val) i j :=
  congrFun (congrFun (induced_rawMatrix g) i) j

end M9Native.ConicFramedGammaAction
