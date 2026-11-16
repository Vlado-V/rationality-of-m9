module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.MatrixSubstitution

/-! Native projective automorphisms with the literal row-coordinate convention.
The polynomial substitution and its inverse are proved, rather than supplied. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry MvPolynomial Matrix
open Stacks.AlgebraicGeometry.ProjPolyChart
open scoped BigOperators

universe u

namespace M9Native.NativeProjectiveLinear

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (n : ℕ)

abbrev coordinateSpace := Fin (n+1) → R
abbrev matrixSpace := Matrix (Fin (n+1)) (Fin (n+1)) R
abbrev generalLinear := Matrix.GeneralLinearGroup (Fin (n+1)) R
abbrev grading := polyGrading R n

def substitution (B : matrixSpace R n) : grading R n →+*ᵍ grading R n :=
  matrixSubstGradedHom R n Bᵀ

@[simp] theorem substitution_C (B : matrixSpace R n) (c : R) :
    substitution R n B (C c) = C c := by simp [substitution]

@[simp] theorem substitution_X (B : matrixSpace R n) (i : Fin (n+1)) :
    substitution R n B (X i) = ∑ j, C (B i j) * X j := by
  simp [substitution]

@[simp] theorem substitution_one :
    substitution R n (1 : matrixSpace R n) = GradedRingHom.id (grading R n) := by
  apply GradedRingHom.toRingHom_injective
  apply MvPolynomial.ringHom_ext
  · exact substitution_C R n 1
  · intro i
    simp [Matrix.one_apply]

theorem substitution_linearForms (B D : matrixSpace R n) (i : Fin (n+1)) :
    substitution R n D (∑ j, C (B i j) * X j) =
      ∑ k, C ((B*D) i k) * X k := by
  simp only [map_sum, map_mul, substitution_C, substitution_X, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.mul_apply, map_sum, Finset.sum_mul, map_mul, mul_assoc]

theorem substitution_comp (B D : matrixSpace R n) :
    (substitution R n D).comp (substitution R n B) = substitution R n (B*D) := by
  apply GradedRingHom.toRingHom_injective
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro i
    change substitution R n D (substitution R n B (X i)) = substitution R n (B*D) (X i)
    rw [substitution_X, substitution_X]
    exact substitution_linearForms R n B D i

theorem evaluation_substitution (B : matrixSpace R n) (v : coordinateSpace R n)
    (p : MvPolynomial (Fin (n+1)) R) :
    MvPolynomial.eval v (substitution R n B p) = MvPolynomial.eval (B *ᵥ v) p := by
  have h : (MvPolynomial.eval v).comp (substitution R n B).toRingHom =
      MvPolynomial.eval (B *ᵥ v) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      simp [Matrix.mulVec, dotProduct]
  exact RingHom.congr_fun h p

theorem irrelevant_le_map_of_inverse (f g : grading R n →+*ᵍ grading R n)
    (hfg : f.comp g = GradedRingHom.id (grading R n)) :
    HomogeneousIdeal.irrelevant (grading R n) ≤
      (HomogeneousIdeal.irrelevant (grading R n)).map f := by
  change (HomogeneousIdeal.irrelevant (grading R n)).toIdeal ≤
    ((HomogeneousIdeal.irrelevant (grading R n)).map f).toIdeal
  apply (HomogeneousIdeal.toIdeal_irrelevant_le (grading R n)).mpr
  intro d hd p hp
  have hg : g p ∈ HomogeneousIdeal.irrelevant (grading R n) :=
    HomogeneousIdeal.mem_irrelevant_of_mem (grading R n) hd (g.map_mem hp)
  have heq : f (g p) = p := congrArg (fun k : grading R n →+*ᵍ grading R n => k p) hfg
  exact heq ▸ Ideal.mem_map_of_mem f.toRingHom hg

theorem substitution_irrelevant_le (B : generalLinear R n) :
    HomogeneousIdeal.irrelevant (grading R n) ≤
      (HomogeneousIdeal.irrelevant (grading R n)).map
        (substitution R n (B : matrixSpace R n)) := by
  apply irrelevant_le_map_of_inverse R n _ (substitution R n (↑B⁻¹ : matrixSpace R n))
  rw [substitution_comp, Units.inv_mul, substitution_one]

/-- This is an actual isomorphism of the native polynomial `Proj` scheme. -/
def projectiveLinear (B : generalLinear R n) :
    AlgebraicGeometry.Proj (grading R n) ≅ AlgebraicGeometry.Proj (grading R n) where
  hom := Proj.map (substitution R n (B : matrixSpace R n)) (substitution_irrelevant_le R n B)
  inv := Proj.map (substitution R n (↑B⁻¹ : matrixSpace R n))
    (substitution_irrelevant_le R n B⁻¹)
  hom_inv_id := by
    rw [← Proj.map_comp]
    simp only [substitution_comp, Units.inv_mul, substitution_one, Proj.map_id]
  inv_hom_id := by
    rw [← Proj.map_comp]
    simp only [substitution_comp, Units.mul_inv, substitution_one, Proj.map_id]

def coordinateGL : (coordinateSpace R n ≃ₗ[R] coordinateSpace R n) ≃* generalLinear R n :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R (coordinateSpace R n)).symm.trans
    Matrix.GeneralLinearGroup.toLin.symm

theorem coordinateGL_mulVec (e : coordinateSpace R n ≃ₗ[R] coordinateSpace R n)
    (v : coordinateSpace R n) :
    (coordinateGL R n e : matrixSpace R n) *ᵥ v = e v := by
  have h := Matrix.GeneralLinearGroup.toLin.apply_symm_apply
    (LinearMap.GeneralLinearGroup.ofLinearEquiv e)
  exact congrArg (fun f : LinearMap.GeneralLinearGroup R (coordinateSpace R n) =>
    (f : Module.End R (coordinateSpace R n)) v) h

end M9Native.NativeProjectiveLinear
