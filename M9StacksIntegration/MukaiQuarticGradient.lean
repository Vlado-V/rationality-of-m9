module

public import M9StacksIntegration.MukaiQuarticNormalForm
public import M9StacksIntegration.MukaiPrimitiveQuartic
public import M9StacksIntegration.MukaiConormalOrigin
public import M9StacksIntegration.MukaiSchubertExpansion

/-!
# The exact determinant coefficient of the native conormal cubic

The coefficient is obtained by tracing the proved adjugate block against
the proved linear polarized block. The output is the actual origin
Plücker evaluation functional on the literal native primitive form space.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open Module Matrix
open scoped BigOperators

namespace M9Native.MukaiQuarticGradient

open LagrangianField MukaiQuarticHitchin MukaiQuarticCubic MukaiQuarticVariation
open MukaiQuarticNormalForm MukaiPrimitiveProjector MukaiConormalPrimitive
open MukaiQuarticComponents
open MukaiPrimitiveQuartic MukaiConormalOrigin

variable (K : Type*) [Field K]

theorem toMatrix_dualBasis (A : Module.End K (DualSix K)) (i j : Fin 6) :
    LinearMap.toMatrix (Pi.basisFun K (Fin 6)).dualBasis
      (Pi.basisFun K (Fin 6)).dualBasis A i j = entry K i j A := by
  have h (j : Fin 6) : (Pi.basisFun K (Fin 6)).dualBasis j = LinearMap.proj j := by
    apply LinearMap.ext
    intro v
    simp
  simp only [LinearMap.toMatrix_apply, Basis.dualBasis_repr, h, entry_apply]
  rw [Pi.basisFun_apply]
  rfl

theorem trace_mul_entry (A B : Module.End K (DualSix K)) :
    LinearMap.trace K (DualSix K) (A*B) =
      ∑ i : Fin 6, ∑ j : Fin 6, entry K i j A * entry K j i B := by
  rw [LinearMap.trace_eq_matrix_trace K (Pi.basisFun K (Fin 6)).dualBasis,
    LinearMap.toMatrix_mul]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, toMatrix_dualBasis]

theorem cofactor_contraction (S : Matrix (Fin 3) (Fin 3) K) :
    (∑ i : Fin 3, ∑ j : Fin 3, S.adjugate j i * S i j) = 3 * S.det := by
  have h (i : Fin 3) : (∑ j : Fin 3, S.adjugate j i * S i j) = S.det := by
    simpa only [mul_comm] using (Matrix.det_eq_sum_mul_adjugate_row S i).symm
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

theorem trace_normal_polar (c : K) (S : Matrix (Fin 3) (Fin 3) K) (r : Coordinates K) :
    LinearMap.trace K (DualSix K)
      (hitchinOperator K (normal K c S) * polarOperator K (normal K c S)
        (coordinateEmbedding K r)) = 12 * r.1 * S.det := by
  rw [trace_mul_entry]
  simp_rw [entry_hitchin_normal]
  have hsum :
      (∑ i : Fin 6, ∑ j : Fin 6, normalEntry K S i j *
        entry K j i (polarOperator K (normal K c S) (coordinateEmbedding K r))) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (-2 * S.adjugate j i) * (-2 * r.1 * S i j) := by
    have hp (i j : Fin 3) :
        entry K (Fin.natAdd 3 j) (Fin.castAdd 3 i)
          (polarOperator K (normal K c S) (coordinateEmbedding K r)) =
          -2 * r.1 * S i j := by
      simpa only [eIndex, fIndex] using entry_polar_normal_embedding K c S r j i
    simp only [Fin.sum_univ_add (a := 3) (b := 3), normalEntry,
      Fin.addCases_left (m := 3) (n := 3), Fin.addCases_right (m := 3) (n := 3),
      zero_mul, Finset.sum_const_zero, zero_add, add_zero, hp]
  rw [hsum]
  calc
    _ = 4 * r.1 * (∑ i : Fin 3, ∑ j : Fin 3, S.adjugate j i * S i j) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [cofactor_contraction]; ring

variable [CharZero K]

theorem cubic_normal_embedding (c : K) (S : Matrix (Fin 3) (Fin 3) K)
    (r : Coordinates K) :
    cubic K (normal K c S) (normal K c S) (normal K c S) (coordinateEmbedding K r) =
      4 * S.det * r.1 := by
  rw [cubic_diagonal, trace_normal_polar]
  field_simp
  ring

theorem aCoordinate_representative (ell : Forms K) :
    aCoordinate K (representative K ell) = ell (originPoint K) := by
  have h := LinearMap.congr_fun
    (primitiveClass_representative K ell) (originPoint K)
  rw [originPoint, MukaiSchubertExpansion.primitiveClass_coordinates] at h
  simpa [originPoint] using h

theorem primitiveCubic_conormalForm (c : K) (S : Symmetric3 K) (ell : Forms K) :
    primitiveCubic K (conormalForm K (c,S)) (conormalForm K (c,S))
      (conormalForm K (c,S)) ell = 4 * S.val.det * ell (originPoint K) := by
  let w : Primitive K := ⟨representative K ell, contraction_representative K ell⟩
  obtain ⟨r, hr⟩ := (primitiveEquiv K).surjective w
  have hrep : representative K ell = coordinateEmbedding K r :=
    (congrArg Subtype.val hr).symm
  simp only [primitiveCubic_apply, representative_conormalForm]
  rw [hrep, cubic_normal_embedding]
  have ha := aCoordinate_representative K ell
  rw [hrep, aCoordinate_embedding] at ha
  rw [ha]

theorem primitiveCubic_conormalForm_linear (c : K) (S : Symmetric3 K) :
    primitiveCubic K (conormalForm K (c,S)) (conormalForm K (c,S))
      (conormalForm K (c,S)) =
      (4 * S.val.det) • Module.Dual.eval K (Primitive K) (originPoint K) := by
  apply LinearMap.ext
  intro ell
  rw [primitiveCubic_conormalForm]
  rfl

def originFunctional : Forms K := (aCoordinate K).comp (Primitive K).subtype

theorem originFunctional_origin : originFunctional K (originPoint K) = 1 := by
  simp [originFunctional, originPoint, primitiveEquiv_val]

theorem primitiveCubic_conormalForm_ne_zero (c : K) (S : Symmetric3 K)
    (hS : S.val.det ≠ 0) :
    primitiveCubic K (conormalForm K (c,S)) (conormalForm K (c,S))
      (conormalForm K (c,S)) ≠ 0 := by
  intro hz
  have h := LinearMap.congr_fun hz (originFunctional K)
  rw [primitiveCubic_conormalForm, originFunctional_origin, mul_one, LinearMap.zero_apply] at h
  exact mul_ne_zero (by norm_num : (4 : K) ≠ 0) hS h

end M9Native.MukaiQuarticGradient
