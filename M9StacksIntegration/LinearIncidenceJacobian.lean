module

public import StacksFrontier.AlgebraicGeometry.GrassmannianScheme.ChartMatrix
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import M9StacksIntegration.LinearIncidenceElimination
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! The actual normalized five linear-incidence equations have an invertible
Jacobian on each open where a nonpivot coefficient is invertible. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory MvPolynomial Matrix Algebra
open scoped BigOperators
universe u
namespace M9Native.LinearIncidenceJacobian
open AlgebraicGeometry.Grassmannian
variable {R : Type u} [CommRing R] (κ : Fin 5 ↪ Fin 14) (v : Fin 14 → R)

abbrev Variables := ChartIndex.{u} (k:=9) (n:=14) κ
abbrev Polynomials : Type u := MvPolynomial (Variables.{u} κ) R

def equations : Fin 5 → Polynomials (R:=R) κ :=
  (chartMatrix (k:=9) (n:=14) κ (MvPolynomial.X : Variables κ → Polynomials (R:=R) κ)).mulVec
    (fun j => MvPolynomial.C (v j))

abbrev Ring := Polynomials (R:=R) κ ⧸ Ideal.span (Set.range (equations κ v))

def coefficient (j : Fin 14) : Ring κ v := algebraMap R (Ring κ v) (v j)

def presentation (w : {j : Fin 14 // j ∉ Set.range κ}) :
    Algebra.PreSubmersivePresentation R (Ring κ v) (Variables.{u} κ) (Fin 5) :=
  Algebra.PreSubmersivePresentation.naive (v:=equations κ v)
    (fun i => ULift.up (w,i)) (by intro i j h;exact congrArg (fun a => a.down.2) h)

theorem pderiv_equations (w : {j : Fin 14 // j ∉ Set.range κ}) (i k : Fin 5) :
    MvPolynomial.pderiv (ULift.up (w,i)) (equations κ v k)=
      if i=k then MvPolynomial.C (v w) else 0 := by
  classical
  simp only [equations,Matrix.mulVec,dotProduct,map_sum,MvPolynomial.pderiv_mul,
    MvPolynomial.pderiv_C,mul_zero,add_zero]
  rw [Finset.sum_eq_single (w : Fin 14)]
  · rw [chartMatrix_apply_of_notMem (k:=9) (n:=14) κ _ k w.property]
    by_cases h : i=k
    · subst k
      simp only [MvPolynomial.pderiv_X_self,one_mul,ite_true]
    · have hi : (ULift.up (w,k) : Variables.{u} κ) ≠ ULift.up (w,i) := by
        intro he
        exact h (congrArg (fun a : Variables.{u} κ => a.down.2) he).symm
      rw [MvPolynomial.pderiv_X_of_ne hi,zero_mul,ite_eq_right h]
  · intro j _ hj
    by_cases hm : j ∈ Set.range κ
    · simp only [chartMatrix,Matrix.of_apply,dite_eq_left hm]
      split_ifs <;> simp
    · rw [chartMatrix_apply_of_notMem (k:=9) (n:=14) κ _ k hm]
      have hi : (ULift.up (w,i) : Variables.{u} κ) ≠ ULift.up (⟨j,hm⟩,k) := by
        intro h
        exact hj (congrArg (fun a : Variables.{u} κ => a.down.1.val) h).symm
      simp [MvPolynomial.pderiv_X,Ne.symm hi]
  · simp

theorem jacobiMatrix (w : {j : Fin 14 // j ∉ Set.range κ}) :
    (presentation κ v w).jacobiMatrix=
      Matrix.diagonal (fun _ : Fin 5 => MvPolynomial.C (v w)) := by
  classical
  ext i j : 1
  rw [presentation,Algebra.PreSubmersivePresentation.jacobiMatrix_naive,Matrix.diagonal_apply]
  exact pderiv_equations κ v w i j

theorem jacobian (w : {j : Fin 14 // j ∉ Set.range κ}) :
    (presentation κ v w).jacobian=coefficient κ v w ^ 5 := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,jacobiMatrix,
    Matrix.det_diagonal]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,map_pow]
  rfl

/-- A genuine presentation of each actual coefficient localization is standard smooth. -/
theorem localization_standardSmooth (w : {j : Fin 14 // j ∉ Set.range κ}) :
    Algebra.IsStandardSmoothOfRelativeDimension 40 R
      (Localization.Away (coefficient κ v w)) := by
  classical
  let B := Ring κ v
  let s : B := coefficient κ v w
  let P := presentation κ v w
  let Q := Algebra.SubmersivePresentation.localizationAway (Localization.Away s) s
  have hJ : IsUnit ((Q.toPreSubmersivePresentation.comp P).jacobian) := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian]
    rw [Algebra.smul_def]
    rw [jacobian,map_pow]
    exact ((IsLocalization.Away.algebraMap_isUnit s).pow 5).mul Q.jacobian_isUnit
  let S : Algebra.SubmersivePresentation R (Localization.Away s)
      (Unit ⊕ Variables.{u} κ) (Unit ⊕ Fin 5) :=
    { __ := Q.toPreSubmersivePresentation.comp P,jacobian_isUnit := hJ }
  apply S.isStandardSmoothOfRelativeDimension
  change Nat.card (Unit ⊕ Variables.{u} κ)-Nat.card (Unit ⊕ Fin 5)=40
  have hcard : Fintype.card (Variables.{u} κ)=45 := by
    change Fintype.card (ULift.{u} ({j : Fin 14 // j ∉ Set.range κ} × Fin 5))=45
    rw [Fintype.card_ulift,Fintype.card_prod,Fintype.card_subtype_compl,
      Fintype.card_fin,Set.card_range_of_injective κ.injective,Fintype.card_fin]
  simp only [Nat.card_eq_fintype_card,Fintype.card_sum,Fintype.card_unit,Fintype.card_fin,hcard]

theorem chartMatrix_pivot_sum (A : Variables.{u} κ → R) (i : Fin 5)
    (inst : Fintype {j : Fin 14 // j ∈ Set.range κ}) :
    (@Finset.univ {j : Fin 14 // j ∈ Set.range κ} inst).sum
      (fun j => chartMatrix (k:=9) (n:=14) κ A i j*v j)=v (κ i) := by
  classical
  letI := inst
  let F : Fin 14 → R := fun j => chartMatrix (k:=9) (n:=14) κ A i j*v j
  have hval (j : Fin 5) : F (κ j)=
      if i=j then v (κ j) else 0 := by
    exact (congrArg (fun x : R => x*v (κ j))
      (chartMatrix_apply_self (k:=9) (n:=14) κ A i j)).trans
      (by split_ifs <;> simp)
  let e : Fin 5 ≃ {j : Fin 14 // j ∈ Set.range κ} := Equiv.ofInjective κ κ.injective
  exact (e.sum_comp
    (fun j : {j : Fin 14 // j ∈ Set.range κ} => F j)).symm.trans
      ((Finset.sum_congr rfl fun j _ => hval j).trans (by simp))

theorem chartMatrix_nonpivot_sum (A : Variables.{u} κ → R) (i : Fin 5) :
    (∑ j : {j : Fin 14 // j ∉ Set.range κ},chartMatrix (k:=9) (n:=14) κ A i j*v j)=
      ∑ j : {j : Fin 14 // j ∉ Set.range κ},A (ULift.up (j,i))*v j :=
  Finset.sum_congr rfl fun j _ => congrArg (fun x => x*v j)
    (chartMatrix_apply_of_notMem (k:=9) (n:=14) κ A i j.property)

theorem chartMatrix_mulVec (A : Variables.{u} κ → R) (i : Fin 5) :
    (chartMatrix (k:=9) (n:=14) κ A).mulVec v i=
      v (κ i)+∑ j : {j : Fin 14 // j ∉ Set.range κ},A (ULift.up (j,i))*v j := by
  classical
  let F : Fin 14 → R := fun j => chartMatrix (k:=9) (n:=14) κ A i j*v j
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun j => j ∈ Set.range κ) F
  exact hsplit.symm.trans (congrArg₂ (fun x y : R => x+y)
    (chartMatrix_pivot_sum κ v A i (Subtype.fintype (fun j => j ∈ Set.range κ)))
      (chartMatrix_nonpivot_sum κ v A i))

theorem equations_eq (i : Fin 5) : equations κ v i=
    MvPolynomial.C (v (κ i))+
      ∑ j : {j : Fin 14 // j ∉ Set.range κ},
        MvPolynomial.X (ULift.up (j,i))*MvPolynomial.C (v j) :=
  chartMatrix_mulVec κ (fun j => MvPolynomial.C (v j)) MvPolynomial.X i

/-- On the actual incidence quotient the nonpivot coefficients generate the unit ideal. -/
theorem nonpivot_span (hfull : Ideal.span (Set.range v)=⊤) :
    Ideal.span (Set.range (fun j : {j : Fin 14 // j ∉ Set.range κ} => coefficient κ v j))=⊤ := by
  classical
  let B := Ring κ v
  let b : Fin 5 → B := fun i => coefficient κ v (κ i)
  let a : {j : Fin 14 // j ∉ Set.range κ} → B := fun j => coefficient κ v j
  let A : Fin 5 → {j : Fin 14 // j ∉ Set.range κ} → B := fun i j =>
    Ideal.Quotient.mk _ (MvPolynomial.X (ULift.up (j,i)))
  have hz (i : Fin 5) : b i+∑ j,A i j*a j=0 := by
    have he := congrArg (Ideal.Quotient.mk (Ideal.span (Set.range (equations κ v))))
      (equations_eq κ v i)
    simp only [map_add,map_sum,map_mul] at he
    have hzero : Ideal.Quotient.mk (Ideal.span (Set.range (equations κ v))) (equations κ v i)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
    exact he.symm.trans hzero
  have hr : Set.range b ∪ Set.range a=Set.range (fun j => coefficient κ v j) := by
    ext x
    constructor
    · rintro (⟨i,rfl⟩|⟨j,rfl⟩)
      · exact ⟨κ i,rfl⟩
      · exact ⟨j,rfl⟩
    · rintro ⟨j,rfl⟩
      by_cases hj : j ∈ Set.range κ
      · obtain ⟨i,rfl⟩ := hj
        exact Or.inl ⟨i,rfl⟩
      · exact Or.inr ⟨⟨j,hj⟩,rfl⟩
  have ht : Ideal.span (Set.range b ∪ Set.range a)=⊤ := by
    rw [hr,show (fun j => coefficient κ v j)=(algebraMap R B) ∘ v from rfl,
      Set.range_comp,← Ideal.map_span,hfull,Ideal.map_top]
  exact M9Native.LinearIncidenceElimination.nonpivot_span_eq_top b a A hz ht

theorem locally_standardSmooth (hfull : Ideal.span (Set.range v)=⊤) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 40) (algebraMap R (Ring κ v)) := by
  refine ⟨Set.range (fun j : {j : Fin 14 // j ∉ Set.range κ} => coefficient κ v j),
    nonpivot_span κ v hfull,?_⟩
  rintro _ ⟨j,rfl⟩
  rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact localization_standardSmooth κ v j

/-- The original quotient spectrum is smooth of relative dimension forty over its base. -/
theorem projection_smoothOfRelativeDimension (hfull : Ideal.span (Set.range v)=⊤) :
    SmoothOfRelativeDimension 40
      (Spec.map (CommRingCat.ofHom (algebraMap R (Ring κ v)))) := by
  rw [HasRingHomProperty.Spec_iff (P:=@SmoothOfRelativeDimension 40)]
  exact locally_standardSmooth κ v hfull

end M9Native.LinearIncidenceJacobian
end
