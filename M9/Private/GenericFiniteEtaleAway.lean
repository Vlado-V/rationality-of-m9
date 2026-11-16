module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Square polynomial quotients away from the Jacobian determinant

Finite-index generalization of the checked Mathlib-only replay of the algebraic core of AxiomMath/Stacks, commit
`c496df0d9beea9deaeabcea8492605f9a0a2313b`,
`StacksFrontier/AlgebraicGeometry/Morphisms/Etale/SquareJacobian.lean`,
Git blob `b64617defcda9fd992909ede9ce5b5381f5f2beb` (Apache-2.0).
This standalone audit leaf imports no Stacks source and is checked against
Mathlib `8accc04827c389e678c3ef83e623b402e7480394` / Lean 4.35.0-rc3.
-/

@[expose] public section
noncomputable section

open MvPolynomial Algebra

namespace M9.FiniteEtaleJacobianReplay

universe u
variable {R : Type u} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

def jacobianDet (v : ι → MvPolynomial (ι) R) : MvPolynomial (ι) R :=
  (Matrix.of fun i j => MvPolynomial.pderiv j (v i)).det

private theorem jacobian_naive (v : ι → MvPolynomial (ι) R) :
    (PreSubmersivePresentation.naive (v := v) id Function.injective_id).jacobian =
      Ideal.Quotient.mk (Ideal.span (Set.range v)) (jacobianDet v) := by
  classical
  have hval : (PreSubmersivePresentation.naive (v := v) id Function.injective_id).val =
      fun i => Ideal.Quotient.mk (Ideal.span (Set.range v)) (X i) :=
    funext fun i => by
      simp [PreSubmersivePresentation.naive_toPresentation, Presentation.naive_toGenerators]
  have halg : (aeval (R := R)
      (fun i => Ideal.Quotient.mk (Ideal.span (Set.range v)) (X i)) :
        MvPolynomial (ι) R →ₐ[R] _) = Ideal.Quotient.mkₐ R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  have hM : (PreSubmersivePresentation.naive (v := v) id Function.injective_id).jacobiMatrix =
      (Matrix.of fun i j => MvPolynomial.pderiv j (v i)).transpose :=
    Matrix.ext fun i j => by
      rw [PreSubmersivePresentation.jacobiMatrix_naive]
      rfl
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Algebra.Generators.algebraMap_apply, hval, hM, Matrix.det_transpose, jacobianDet]
  exact DFunLike.congr_fun halg _

/-- The actual localized polynomial quotient is étale over its coefficient ring. -/
theorem etale_away_jacobianDet (v : ι → MvPolynomial (ι) R)
    {I : Ideal (MvPolynomial (ι) R)} (hI : I = Ideal.span (Set.range v)) (T : Type u)
    [CommRing T] [Algebra (MvPolynomial (ι) R ⧸ I) T]
    [IsLocalization.Away (Ideal.Quotient.mk I (jacobianDet v)) T] :
    RingHom.Etale ((algebraMap (MvPolynomial (ι) R ⧸ I) T).comp
      (algebraMap R (MvPolynomial (ι) R ⧸ I))) := by
  classical
  subst hI
  let d : MvPolynomial (ι) R ⧸ Ideal.span (Set.range v) :=
    Ideal.Quotient.mk (Ideal.span (Set.range v)) (jacobianDet v)
  let P : PreSubmersivePresentation R (MvPolynomial (ι) R ⧸ Ideal.span (Set.range v))
      (ι) (ι) := PreSubmersivePresentation.naive id Function.injective_id
  let Q : PreSubmersivePresentation (MvPolynomial (ι) R ⧸ Ideal.span (Set.range v)) T
      Unit Unit := PreSubmersivePresentation.localizationAway T d
  let _ : Algebra R T :=
    ((algebraMap (MvPolynomial (ι) R ⧸ Ideal.span (Set.range v)) T).comp
      (algebraMap R (MvPolynomial (ι) R ⧸ Ideal.span (Set.range v)))).toAlgebra
  have _ : IsScalarTower R (MvPolynomial (ι) R ⧸ Ideal.span (Set.range v)) T :=
    IsScalarTower.of_algebraMap_eq (R := R)
      (S := MvPolynomial (ι) R ⧸ Ideal.span (Set.range v)) (A := T) fun _ => rfl
  have hunit : IsUnit ((Q.comp P).jacobian) := by
    rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      show P.jacobian = d from jacobian_naive v,
      show Q.jacobian = algebraMap _ T d from
        PreSubmersivePresentation.localizationAway_jacobian (S := T) d,
      Algebra.smul_def]
    exact (IsLocalization.Away.algebraMap_isUnit (S := T) d).mul
      (IsLocalization.Away.algebraMap_isUnit (S := T) d)
  have _ : Algebra.IsStandardSmoothOfRelativeDimension 0 R T :=
    SubmersivePresentation.isStandardSmoothOfRelativeDimension
      { __ := Q.comp P, jacobian_isUnit := hunit } (by simp [Algebra.Presentation.dimension])
  exact (inferInstance : Algebra.Etale R T)

end M9.FiniteEtaleJacobianReplay

#print axioms M9.FiniteEtaleJacobianReplay.etale_away_jacobianDet
