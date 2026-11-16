module

public import Mathlib.LinearAlgebra.SymplecticGroup
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The coordinate ring representing genuine symplectic matrices

The defining equations are the entries of `X J Xᵀ - J`. The result is a
natural equivalence between ring maps from the quotient coordinate ring
and the actual Mathlib symplectic group over every commutative ring.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open Matrix

universe u

namespace M9Native.Sp6CoordinateRing

abbrev Index := Fin 3 ⊕ Fin 3
abbrev Polynomial : Type u := MvPolynomial (Index × Index) (ULift.{u} ℤ)

def genericMatrix : Matrix Index Index Polynomial := Matrix.mvPolynomialX _ _ _

def equation (ij : Index × Index) : Polynomial :=
  (genericMatrix * Matrix.J (Fin 3) Polynomial * genericMatrix.transpose -
    Matrix.J (Fin 3) Polynomial) ij.1 ij.2

def relations : Ideal Polynomial := Ideal.span (Set.range equation)

abbrev CoordinateRing : Type u := Polynomial ⧸ relations

/-- Rebundle the quotient map at the polynomial semiring instance used by evaluation. -/
def quotientMap : Polynomial →+* CoordinateRing where
  toFun p := Ideal.Quotient.mk relations p
  map_one' := (Ideal.Quotient.mk relations).map_one
  map_mul' p q := (Ideal.Quotient.mk relations).map_mul p q
  map_zero' := (Ideal.Quotient.mk relations).map_zero
  map_add' p q := (Ideal.Quotient.mk relations).map_add p q

def coordinate (i j : Index) : CoordinateRing :=
  Ideal.Quotient.mk relations (MvPolynomial.X (i,j))

def universalMatrix : Matrix Index Index CoordinateRing :=
  fun i j => coordinate i j

theorem map_genericMatrix {R : Type u} [CommRing R] (f : Polynomial →+* R) :
    genericMatrix.map f = Matrix.of (fun i j => f (MvPolynomial.X (i,j))) := rfl

theorem map_equation {R : Type u} [CommRing R] (f : Polynomial →+* R)
    (ij : Index × Index) :
    f (equation ij) =
      ((genericMatrix.map f) * Matrix.J (Fin 3) R * (genericMatrix.map f).transpose -
        Matrix.J (Fin 3) R) ij.1 ij.2 := by
  change ((genericMatrix * Matrix.J (Fin 3) Polynomial * genericMatrix.transpose -
    Matrix.J (Fin 3) Polynomial).map f) ij.1 ij.2 = _
  rw [Matrix.map_sub, Matrix.map_mul, Matrix.map_mul, Matrix.map_J, Matrix.transpose_map]
  exact map_sub f

theorem universalMatrix_symplectic : universalMatrix ∈ Matrix.symplecticGroup (Fin 3) CoordinateRing := by
  rw [SymplecticGroup.mem_iff, ← sub_eq_zero]
  ext i j
  change (universalMatrix * Matrix.J (Fin 3) CoordinateRing * universalMatrix.transpose -
    Matrix.J (Fin 3) CoordinateRing) i j = 0
  have h : Ideal.Quotient.mk relations (equation (i,j)) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr
    (Ideal.subset_span (show equation (i,j) ∈ Set.range equation from ⟨(i,j),rfl⟩))
  have hM : genericMatrix.map quotientMap = universalMatrix := by
    ext a b
    rfl
  have he := map_equation (R := CoordinateRing) quotientMap (i,j)
  rw [hM] at he
  exact he.symm.trans h

def universal : Matrix.symplecticGroup (Fin 3) CoordinateRing :=
  ⟨universalMatrix, universalMatrix_symplectic⟩

variable (R : Type u) [CommRing R]

def polynomialEvaluation (M : Matrix Index Index R) : Polynomial →+* R :=
  MvPolynomial.eval₂Hom ((algebraMap ℤ R).comp ULift.ringEquiv.toRingHom)
    (fun ij => M ij.1 ij.2)

theorem polynomialEvaluation_X (M : Matrix Index Index R) (i j : Index) :
    polynomialEvaluation R M (MvPolynomial.X (i,j)) = M i j := by
  simp [polynomialEvaluation]

theorem genericMatrix_evaluation (M : Matrix Index Index R) :
    genericMatrix.map (polynomialEvaluation R M) = M := by
  ext i j
  exact polynomialEvaluation_X R M i j

def evaluation (g : Matrix.symplecticGroup (Fin 3) R) : CoordinateRing →+* R :=
  Ideal.Quotient.lift relations (polynomialEvaluation R (g : Matrix Index Index R)) (by
    have h : relations ≤ RingHom.ker (polynomialEvaluation R (g : Matrix Index Index R)) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨ij,rfl⟩
      change polynomialEvaluation R (g : Matrix Index Index R) (equation ij) = 0
      rw [map_equation, genericMatrix_evaluation]
      exact congrFun (congrFun (sub_eq_zero.mpr (SymplecticGroup.mem_iff.mp g.property)) ij.1) ij.2
    intro p hp
    exact h hp)

@[simp] theorem evaluation_coordinate (g : Matrix.symplecticGroup (Fin 3) R) (i j : Index) :
    evaluation R g (coordinate i j) = (g : Matrix Index Index R) i j := by
  change (Ideal.Quotient.lift relations _ _) (Ideal.Quotient.mk relations _) = _
  rw [Ideal.Quotient.lift_mk]
  exact polynomialEvaluation_X R _ i j

/-- A coordinate-ring homomorphism gives a genuine symplectic matrix, with no reducedness
or field hypothesis on the target ring. -/
def matrixOfHom (f : CoordinateRing →+* R) : Matrix.symplecticGroup (Fin 3) R :=
  ⟨universalMatrix.map f, SymplecticGroup.map_mem universalMatrix_symplectic f⟩

@[simp] theorem matrixOfHom_apply (f : CoordinateRing →+* R) (i j : Index) :
    (matrixOfHom R f : Matrix Index Index R) i j = f (coordinate i j) := rfl

private theorem coefficient_hom_unique (f g : ULift.{u} ℤ →+* R) : f = g := by
  have h : f.comp ULift.ringEquiv.symm.toRingHom =
      g.comp ULift.ringEquiv.symm.toRingHom := RingHom.ext_int _ _
  ext z
  exact congrArg (fun q : ℤ →+* R => q (ULift.ringEquiv z)) h

/-- The actual symplectic group is represented by the displayed polynomial quotient. -/
def homEquiv : (CoordinateRing →+* R) ≃ Matrix.symplecticGroup (Fin 3) R where
  toFun := matrixOfHom R
  invFun := evaluation R
  left_inv f := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext'
    · exact coefficient_hom_unique R _ _
    · intro ij
      change evaluation R (matrixOfHom R f) (coordinate ij.1 ij.2) =
        f (coordinate ij.1 ij.2)
      rw [evaluation_coordinate, matrixOfHom_apply]
  right_inv g := by
    apply Subtype.ext
    ext i j
    exact evaluation_coordinate R g i j

@[simp] theorem homEquiv_apply (f : CoordinateRing →+* R) (i j : Index) :
    (homEquiv R f : Matrix Index Index R) i j = f (coordinate i j) := rfl

/-- The representing equivalence is natural for every homomorphism of coefficient rings. -/
theorem homEquiv_comp {S : Type u} [CommRing S] (f : CoordinateRing →+* R) (ρ : R →+* S) :
    (homEquiv S (ρ.comp f) : Matrix Index Index S) = (homEquiv R f).val.map ρ := rfl

end M9Native.Sp6CoordinateRing
