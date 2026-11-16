module

public import M9.CayleyTransform
public import M9.SemilinearInvolution
public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.Tactic

/-! The actual sixteen-variable graph function field and its Cayley coordinates.
Algebraic independence is deduced from the proved rational inverse and the
transcendence degree of the original independent variables. -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9.CayleyField

open Matrix MvPolynomial IntermediateField

abbrev Coordinate := Fin 4 × Fin 4
abbrev Polynomial (L : Type*) [Field L] := MvPolynomial Coordinate L
abbrev Rational (L : Type*) [Field L] := FractionRing (Polynomial L)

variable (L : Type*) [Field L] [CharZero L]

def polynomialMatrix : Matrix (Fin 4) (Fin 4) (Polynomial L) := fun i j => X (i,j)

def genericMatrix : Matrix (Fin 4) (Fin 4) (Rational L) :=
  fun i j => algebraMap (Polynomial L) (Rational L) (X (i,j))

def genericCoordinate (ij : Coordinate) : Rational L := genericMatrix L ij.1 ij.2

theorem polynomialMatrix_det_ne_zero : (polynomialMatrix L).det ≠ 0 := by
  intro h
  let ev : Polynomial L →+* L := MvPolynomial.eval (fun ij : Coordinate =>
    (1 : Matrix (Fin 4) (Fin 4) L) ij.1 ij.2)
  have hm : ev.mapMatrix (polynomialMatrix L) = 1 := by
    ext i j
    simp [ev, polynomialMatrix]
  have hh := congrArg ev h
  rw [map_zero, ev.map_det, hm, Matrix.det_one] at hh
  exact one_ne_zero hh

theorem polynomialMatrix_add_one_det_ne_zero : (polynomialMatrix L + 1).det ≠ 0 := by
  intro h
  let ev : Polynomial L →+* L := MvPolynomial.eval (fun _ : Coordinate => 0)
  have hm : ev.mapMatrix (polynomialMatrix L + 1) = 1 := by
    ext i j
    simp [ev, polynomialMatrix, map_add, Matrix.map_one]
  have hh := congrArg ev h
  rw [map_zero, ev.map_det, hm, Matrix.det_one] at hh
  exact one_ne_zero hh

theorem genericMatrix_det_ne_zero : (genericMatrix L).det ≠ 0 := by
  have hm : (algebraMap (Polynomial L) (Rational L)).mapMatrix (polynomialMatrix L) =
      genericMatrix L := rfl
  rw [← hm, ← RingHom.map_det]
  exact (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial L) (Rational L))).mpr
    (polynomialMatrix_det_ne_zero L)

theorem genericMatrix_add_one_det_ne_zero : (genericMatrix L + 1).det ≠ 0 := by
  have hm : (algebraMap (Polynomial L) (Rational L)).mapMatrix (polynomialMatrix L + 1) =
      genericMatrix L + 1 := by
    rw [map_add, map_one]
    rfl
  rw [← hm, ← RingHom.map_det]
  exact (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial L) (Rational L))).mpr
    (polynomialMatrix_add_one_det_ne_zero L)

omit [CharZero L] in
theorem genericCoordinate_independent : AlgebraicIndependent L (genericCoordinate L) := by
  exact (MvPolynomial.algebraicIndependent_X Coordinate L).map'
    (f := IsScalarTower.toAlgHom L (Polynomial L) (Rational L))
    (IsFractionRing.injective (Polynomial L) (Rational L))

omit [CharZero L] in
theorem eq_top_of_generic_mem (S : IntermediateField L (Rational L))
    (hx : ∀ ij, genericCoordinate L ij ∈ S) : S = ⊤ := by
  have hp : ∀ p : Polynomial L, algebraMap (Polynomial L) (Rational L) p ∈ S := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      change algebraMap L (Rational L) a ∈ S
      exact S.algebraMap_mem a
    | add p q hp hq => simpa only [map_add] using S.add_mem hp hq
    | mul_X p i hp =>
      simpa only [map_mul, genericCoordinate, genericMatrix, Prod.mk.eta] using S.mul_mem hp (hx i)
  apply top_unique
  intro x _
  obtain ⟨p,q,hq,rfl⟩ := IsFractionRing.div_surjective (Polynomial L) x
  exact S.div_mem (hp p) (hp q)

omit [CharZero L] in
theorem genericCoordinate_adjoin :
    IntermediateField.adjoin L (Set.range (genericCoordinate L)) = ⊤ :=
  eq_top_of_generic_mem L _ fun ij => subset_adjoin L _ ⟨ij,rfl⟩

omit [CharZero L] in
/-- Every entry of an inverse matrix belongs to any intermediate field
containing its entries, when the determinant is nonzero. -/
theorem matrix_inverse_mem (S : IntermediateField L (Rational L))
    (A : Matrix (Fin 4) (Fin 4) (Rational L)) (hA : A.det ≠ 0)
    (hmem : ∀ i j, A i j ∈ S) : ∀ i j, A⁻¹ i j ∈ S := by
  let B : Matrix (Fin 4) (Fin 4) S := fun i j => ⟨A i j,hmem i j⟩
  have hm : S.val.toRingHom.mapMatrix B = A := rfl
  have hb : B.det ≠ 0 := by
    intro hz
    apply hA
    have hh := congrArg S.val hz
    rw [S.val.map_det, map_zero] at hh
    change (S.val.toRingHom.mapMatrix B).det = 0 at hh
    rw [hm] at hh
    exact hh
  have hi := M9.map_matrix_inverse S.val.toRingHom B hb
  rw [hm] at hi
  intro i j
  rw [← hi]
  exact (B⁻¹ i j).property

def cayleyCoordinate (ij : Coordinate) : Rational L := cayley (genericMatrix L) ij.1 ij.2

theorem cayleyCoordinate_adjoin :
    IntermediateField.adjoin L (Set.range (cayleyCoordinate L)) = ⊤ := by
  let S := IntermediateField.adjoin L (Set.range (cayleyCoordinate L))
  have hc : ∀ i j, cayley (genericMatrix L) i j ∈ S :=
    fun i j => subset_adjoin L _ ⟨(i,j),rfl⟩
  have hminus : ∀ i j, (1 - cayley (genericMatrix L)) i j ∈ S := by
    intro i j
    apply S.sub_mem ?_ (hc i j)
    by_cases h : i=j <;> simp [Matrix.one_apply,h]
  have hinv := matrix_inverse_mem L S (1 - cayley (genericMatrix L))
    (one_sub_cayley_det_ne_zero _ (genericMatrix_add_one_det_ne_zero L)) hminus
  have hback : ∀ i j, inverseCayley (cayley (genericMatrix L)) i j ∈ S := by
    intro i j
    rw [inverseCayley, Matrix.mul_apply]
    apply S.sum_mem
    intro k _
    apply S.mul_mem (hinv i k)
    apply S.add_mem ?_ (hc k j)
    by_cases h : k=j <;> simp [Matrix.one_apply,h]
  apply eq_top_of_generic_mem L S
  rintro ⟨i,j⟩
  have h := hback i j
  rw [inverseCayley_cayley _ (genericMatrix_add_one_det_ne_zero L)] at h
  exact h

omit [CharZero L] in
/-- A generating family of sixteen elements in this actual rational field is
independent: the transcendence degree lower bound comes from the original Xs. -/
theorem independent_of_adjoin_eq_top (x : Coordinate → Rational L)
    (hgen : IntermediateField.adjoin L (Set.range x) = ⊤) :
    AlgebraicIndependent L x := by
  have : IsFractionRing (Algebra.adjoin L (Set.range x)) (Rational L) :=
    IsFractionRing.of_field _ _ fun z => by
      have hz : z ∈ IntermediateField.adjoin L (Set.range x) := by rw [hgen]; trivial
      obtain ⟨p,hp,q,hq,heq⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
      exact ⟨⟨p,hp⟩,⟨q,hq⟩,heq⟩
  have : Algebra.IsAlgebraic (Algebra.adjoin L (Set.range x)) (Rational L) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (Algebra.adjoin L (Set.range x)))
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite L x
    (genericCoordinate_independent L).lift_cardinalMk_le_trdeg).1

theorem cayleyCoordinate_independent : AlgebraicIndependent L (cayleyCoordinate L) :=
  independent_of_adjoin_eq_top L _ (cayleyCoordinate_adjoin L)

/-- Actual L-algebra coordinate change to the sixteen Cayley variables. -/
def cayleyAlgEquiv : Rational L ≃ₐ[L] Rational L :=
  (cayleyCoordinate_independent L).aevalEquivField |>.trans
    ((IntermediateField.equivOfEq (cayleyCoordinate_adjoin L)).trans IntermediateField.topEquiv)

theorem cayleyAlgEquiv_variable (ij : Coordinate) :
    cayleyAlgEquiv L (genericCoordinate L ij) = cayleyCoordinate L ij := by
  change ((cayleyCoordinate_independent L).aevalEquivField
    (algebraMap (Polynomial L) (Rational L) (X ij)) : Rational L) = _
  rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
  simp

def normalizedCoordinate (θ : L) (ij : Coordinate) : Rational L :=
  (algebraMap L (Rational L) θ)⁻¹ * cayleyCoordinate L ij

theorem normalizedCoordinate_adjoin (θ : L) (hθ : θ ≠ 0) :
    IntermediateField.adjoin L (Set.range (normalizedCoordinate L θ)) = ⊤ := by
  apply top_unique
  rw [← cayleyCoordinate_adjoin L]
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨ij,rfl⟩
  change cayleyCoordinate L ij ∈ IntermediateField.adjoin L (Set.range (normalizedCoordinate L θ))
  have hmem := IntermediateField.subset_adjoin L (Set.range (normalizedCoordinate L θ)) ⟨ij,rfl⟩
  have hconst := (IntermediateField.adjoin L (Set.range (normalizedCoordinate L θ))).algebraMap_mem θ
  have hθ' : algebraMap L (Rational L) θ ≠ 0 :=
    (map_ne_zero (algebraMap L (Rational L))).mpr hθ
  simpa only [normalizedCoordinate, ← mul_assoc, mul_inv_cancel₀ hθ', one_mul] using
    (IntermediateField.adjoin L (Set.range (normalizedCoordinate L θ))).mul_mem hconst hmem

theorem normalizedCoordinate_independent (θ : L) (hθ : θ ≠ 0) :
    AlgebraicIndependent L (normalizedCoordinate L θ) :=
  independent_of_adjoin_eq_top L _ (normalizedCoordinate_adjoin L θ hθ)

/-- The concrete L-algebra equivalence sending free coordinates to C/theta. -/
def normalizedAlgEquiv (θ : L) (hθ : θ ≠ 0) : Rational L ≃ₐ[L] Rational L :=
  (normalizedCoordinate_independent L θ hθ).aevalEquivField |>.trans
    ((IntermediateField.equivOfEq (normalizedCoordinate_adjoin L θ hθ)).trans IntermediateField.topEquiv)

theorem normalizedAlgEquiv_variable (θ : L) (hθ : θ ≠ 0) (ij : Coordinate) :
    normalizedAlgEquiv L θ hθ (genericCoordinate L ij) = normalizedCoordinate L θ ij := by
  change ((normalizedCoordinate_independent L θ hθ).aevalEquivField
    (algebraMap (Polynomial L) (Rational L) (X ij)) : Rational L) = _
  rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
  simp

end M9.CayleyField
