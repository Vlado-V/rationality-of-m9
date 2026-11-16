module

public import M9.MovingDualDeterminantFrames
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Basic

/-!
# Scalar extension of the actual determinant-twisted standard four-plane

The source is the literal K⊗ℂE0 used in finite descent. The target is the
literal S0_K⊗(⋀⁴S0_K)∨ in the actual coefficient-extended symmetric matrices.
The comparison retains pure tensors and original coefficient embeddings.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 2048
open scoped Classical TensorProduct Matrix

namespace M9.DeterminantFrameScalarExtension
open Module StandardFourPlaneRepresentation MovingDeterminantFrames

local instance standardPlaneGroup : AddCommGroup S0 :=
  { S0.addCommGroup with toAddCommMonoid := S0.addCommMonoid }

variable (K : Type*) [Field K] [Algebra ℂ K]

local instance planeGroup (S : Submodule K (M9.Symmetric3 K)) : AddCommGroup S :=
  { S.addCommGroup with toAddCommMonoid := S.addCommMonoid }

/-- The actual scalar extension of symmetric matrices, through their six
literal independent entries. -/
def symmetricBaseChangeEquiv : (K ⊗[ℂ] M9.Symmetric3 ℂ) ≃ₗ[K] M9.Symmetric3 K :=
  ((M9.symmetric3Coordinates ℂ).baseChange ℂ K (M9.Symmetric3 ℂ) (M9.Upper3 → ℂ)).trans
    ((TensorProduct.piScalarRight ℂ K K M9.Upper3).trans (M9.symmetric3Coordinates K).symm)

theorem symmetricBaseChangeEquiv_tmul_upper (a : K) (q : M9.Symmetric3 ℂ) (ij : M9.Upper3) :
    (M9.symmetric3Coordinates K (symmetricBaseChangeEquiv K (a ⊗ₜ[ℂ] q))) ij =
      algebraMap ℂ K (q.val ij.val.1 ij.val.2) * a := by
  simp only [symmetricBaseChangeEquiv, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
    LinearEquiv.apply_symm_apply, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  rw [Algebra.smul_def]
  rfl

theorem symmetricBaseChangeEquiv_tmul_entry (a : K) (q : M9.Symmetric3 ℂ) (i j : Fin 3) :
    (symmetricBaseChangeEquiv K (a ⊗ₜ[ℂ] q)).val i j = algebraMap ℂ K (q.val i j) * a := by
  by_cases hij : i ≤ j
  · exact symmetricBaseChangeEquiv_tmul_upper K a q ⟨(i,j),hij⟩
  · have hji : j ≤ i := le_of_not_ge hij
    have he := symmetricBaseChangeEquiv_tmul_upper K a q ⟨(j,i),hji⟩
    change (symmetricBaseChangeEquiv K (a ⊗ₜ[ℂ] q)).val j i = algebraMap ℂ K (q.val j i) * a at he
    have hq : q.val j i = q.val i j := congrFun (congrFun q.property i) j
    have ho : (symmetricBaseChangeEquiv K (a ⊗ₜ[ℂ] q)).val j i =
        (symmetricBaseChangeEquiv K (a ⊗ₜ[ℂ] q)).val i j :=
      congrFun (congrFun (symmetricBaseChangeEquiv K (a ⊗ₜ[ℂ] q)).property i) j
    rw [ho,hq] at he
    exact he

/-- Literal coefficient extension of the original standard-plane inclusion. -/
def standardPlaneEmbedding : (K ⊗[ℂ] S0) →ₗ[K] M9.Symmetric3 K :=
  (symmetricBaseChangeEquiv K).toLinearMap.comp (S0.subtype.baseChange K)

theorem standardPlaneEmbedding_injective : Function.Injective (standardPlaneEmbedding K) := by
  apply (symmetricBaseChangeEquiv K).injective.comp
  change Function.Injective (S0.subtype.baseChange K : K ⊗[ℂ] S0 → K ⊗[ℂ] M9.Symmetric3 ℂ)
  rw [LinearMap.baseChange_eq_ltensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := K) S0.subtype S0.injective_subtype

/-- The actual scalar-extended four-plane, embedded in Symmetric3 K. -/
def standardPlane : Submodule K (M9.Symmetric3 K) := (standardPlaneEmbedding K).range

def standardPlaneFrame : (K ⊗[ℂ] S0) ≃ₗ[K] standardPlane K :=
  LinearEquiv.ofInjective (standardPlaneEmbedding K) (standardPlaneEmbedding_injective K)

@[simp] theorem standardPlaneFrame_tmul_entry (a : K) (q : S0) (i j : Fin 3) :
    (standardPlaneFrame K (a ⊗ₜ[ℂ] q)).val.val i j = algebraMap ℂ K (q.val.val i j) * a := by
  change (symmetricBaseChangeEquiv K ((S0.subtype.baseChange K) (a ⊗ₜ[ℂ] q))).val i j = _
  rw [LinearMap.baseChange_tmul]
  exact symmetricBaseChangeEquiv_tmul_entry K a q.val i j

def standardPlaneBasis : Basis (Fin 4) K (standardPlane K) :=
  (evaluationBasis.baseChange K).map (standardPlaneFrame K)

theorem standardPlaneBasis_coordinates (a : K) (q : S0) (i : Fin 4) :
    (standardPlaneBasis K).equivFun (standardPlaneFrame K (a ⊗ₜ[ℂ] q)) i =
      algebraMap ℂ K (evaluationEquiv q i) * a := by
  change (evaluationBasis.baseChange K).repr
    ((standardPlaneFrame K).symm (standardPlaneFrame K (a ⊗ₜ[ℂ] q))) i = _
  rw [LinearEquiv.symm_apply_apply, Basis.baseChange_repr_tmul]
  have hb : evaluationBasis.repr q i = evaluationEquiv q i := by
    change (Pi.basisFun ℂ (Fin 4)).repr (evaluationEquiv q) i = _
    simp
  rw [hb, Algebra.smul_def]

def rawCoordinates : (K ⊗[ℂ] E0) ≃ₗ[K] (Fin 4 → K) :=
  (tensorEvaluationEquiv.baseChange ℂ K E0 (Fin 4 → ℂ)).trans
    (TensorProduct.piScalarRight ℂ K K (Fin 4))

theorem rawCoordinates_tmul (a : K) (x : E0) (i : Fin 4) :
    rawCoordinates K (a ⊗ₜ[ℂ] x) i = algebraMap ℂ K (tensorEvaluationEquiv x i) * a := by
  simp only [rawCoordinates, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  rw [Algebra.smul_def]

def twistedCoordinates : Twisted K (standardPlane K) ≃ₗ[K] (Fin 4 → K) :=
  (tensorTrivialization (standardPlaneBasis K)).trans (standardPlaneBasis K).equivFun

/-- Coefficient extension of an actual top dual form, normalized by the
actual scalar-extended basis volume. -/
def scalarExtendedDual (φ : StandardFourPlaneRepresentation.DeterminantDual) :
    MovingDeterminantFrames.DeterminantDual K (standardPlane K) :=
  (MovingDeterminantFrames.determinantDualCoordinates (standardPlaneBasis K)).symm
    (algebraMap ℂ K (StandardFourPlaneRepresentation.determinantDualCoordinates φ))

/-- An actual scalar-extension equivalence between the literal finite-descent
tensor and the actual determinant-twisted scalar-extended plane. -/
def rawToTwisted : (K ⊗[ℂ] E0) ≃ₗ[K] Twisted K (standardPlane K) :=
  (rawCoordinates K).trans (twistedCoordinates K).symm

/-- The comparison preserves original pure tensors and their original
complex coefficient inclusion. -/
theorem rawToTwisted_tmul_tmul (a : K) (q : S0)
    (φ : StandardFourPlaneRepresentation.DeterminantDual) :
    rawToTwisted K (a ⊗ₜ[ℂ] (q ⊗ₜ[ℂ] φ)) =
      standardPlaneFrame K (a ⊗ₜ[ℂ] q) ⊗ₜ[K] scalarExtendedDual K φ := by
  apply (twistedCoordinates K).injective
  change twistedCoordinates K ((twistedCoordinates K).symm
    (rawCoordinates K (a ⊗ₜ[ℂ] (q ⊗ₜ[ℂ] φ)))) = _
  rw [LinearEquiv.apply_symm_apply]
  ext i
  rw [rawCoordinates_tmul, tensorEvaluationEquiv_tmul]
  change algebraMap ℂ K (StandardFourPlaneRepresentation.determinantDualCoordinates φ * evaluationEquiv q i) * a =
    (standardPlaneBasis K).equivFun
      (MovingDeterminantFrames.determinantDualCoordinates (standardPlaneBasis K) (scalarExtendedDual K φ) •
        standardPlaneFrame K (a ⊗ₜ[ℂ] q)) i
  rw [scalarExtendedDual, LinearEquiv.apply_symm_apply, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [standardPlaneBasis_coordinates, map_mul, mul_assoc]


def baseVector (q : S0) : standardPlane K := standardPlaneFrame K (1 ⊗ₜ[ℂ] q)

theorem evaluationBasis_repr (q : S0) (i : Fin 4) : evaluationBasis.repr q i = evaluationEquiv q i := by
  change (Pi.basisFun ℂ (Fin 4)).repr (evaluationEquiv q) i = _
  simp

theorem baseVector_repr (q : S0) (i : Fin 4) :
    (standardPlaneBasis K).repr (baseVector K q) i = algebraMap ℂ K (evaluationBasis.repr q i) := by
  change (standardPlaneBasis K).equivFun (standardPlaneFrame K (1 ⊗ₜ[ℂ] q)) i = _
  rw [standardPlaneBasis_coordinates, mul_one, evaluationBasis_repr]

theorem baseVector_det (v : Fin 4 → S0) :
    (standardPlaneBasis K).det (fun i => baseVector K (v i)) = algebraMap ℂ K (evaluationBasis.det v) := by
  rw [Basis.det_apply, Basis.det_apply]
  have hm : (standardPlaneBasis K).toMatrix (fun i => baseVector K (v i)) =
      (evaluationBasis.toMatrix v).map (algebraMap ℂ K) := by
    ext i j
    exact baseVector_repr K (v j) i
  rw [hm]
  exact ((algebraMap ℂ K).map_det (evaluationBasis.toMatrix v)).symm

/-- The extended top form is the actual coefficient extension on every
original exterior product, not just a chosen one-dimensional stand-in. -/
theorem scalarExtendedDual_eval (φ : StandardFourPlaneRepresentation.DeterminantDual) (v : Fin 4 → S0) :
    scalarExtendedDual K φ (exteriorPower.ιMulti K 4 (fun i => baseVector K (v i))) =
      algebraMap ℂ K (φ (exteriorPower.ιMulti ℂ 4 v)) := by
  have hk : scalarExtendedDual K φ = exteriorPower.alternatingMapLinearEquiv
      (algebraMap ℂ K (StandardFourPlaneRepresentation.determinantDualCoordinates φ) •
        (standardPlaneBasis K).det) := by
    apply (MovingDeterminantFrames.determinantDualCoordinates (standardPlaneBasis K)).injective
    rw [scalarExtendedDual, LinearEquiv.apply_symm_apply, MovingDeterminantFrames.determinantDualCoordinates_apply,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    simp only [AlternatingMap.smul_apply, smul_eq_mul, Basis.det_self, mul_one]
  let a : S0 [⋀^Fin 4]→ₗ[ℂ] ℂ := exteriorPower.alternatingMapLinearEquiv.symm φ
  have hc := congrArg (fun η : S0 [⋀^Fin 4]→ₗ[ℂ] ℂ => η v) (a.eq_smul_basis_det evaluationBasis)
  change φ (exteriorPower.ιMulti ℂ 4 v) =
    φ (exteriorPower.ιMulti ℂ 4 evaluationBasis) * evaluationBasis.det v at hc
  rw [← StandardFourPlaneRepresentation.determinantDualCoordinates_apply] at hc
  rw [hk, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, AlternatingMap.smul_apply,
    smul_eq_mul, baseVector_det, ← map_mul, ← hc]

end M9.DeterminantFrameScalarExtension
