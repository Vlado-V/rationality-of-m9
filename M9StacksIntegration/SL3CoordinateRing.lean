module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Algebra.Ring.Hom.InjSurj

/-!
# The genuine determinant-one coordinate ring of SL3

The algebra is the quotient of the nine matrix-entry polynomial ring
by det(X)-1. Its points are literal Mathlib special-linear matrices.
The first-row normalization into the actual GL3 determinant localization
has an actual specialization left inverse, proving the quotient is a
domain over every field without an irreducibility premise.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Matrix

universe u v w

namespace M9Native.SL3CoordinateRing

abbrev Index := Fin 3
abbrev Variable := Index × Index

section Basic

variable (K : Type u) [CommRing K]

abbrev Polynomial := MvPolynomial Variable K

def genericMatrix : Matrix Index Index (Polynomial K) := Matrix.mvPolynomialX _ _ _
def determinant : Polynomial K := (genericMatrix K).det
def relation : Polynomial K := determinant K-1
def relations : Ideal (Polynomial K) := Ideal.span ({relation K} : Set (Polynomial K))
abbrev CoordinateRing := Polynomial K ⧸ relations K

def quotientMap : Polynomial K →ₐ[K] CoordinateRing K := Ideal.Quotient.mkₐ K (relations K)
def coordinate (i j : Index) : CoordinateRing K := quotientMap K (MvPolynomial.X (i,j))
def universalMatrix : Matrix Index Index (CoordinateRing K) := fun i j => coordinate K i j

theorem genericMatrix_quotient : (quotientMap K).mapMatrix (genericMatrix K) = universalMatrix K := rfl

theorem quotientMap_determinant : quotientMap K (determinant K) = (universalMatrix K).det := by
  rw [determinant,AlgHom.map_det,genericMatrix_quotient]

theorem universalMatrix_det : (universalMatrix K).det = 1 := by
  have h : quotientMap K (relation K) = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (Set.mem_singleton (relation K)))
  rw [relation,map_sub,map_one,quotientMap_determinant,sub_eq_zero] at h
  exact h

def universal : Matrix.SpecialLinearGroup Index (CoordinateRing K) :=
  ⟨universalMatrix K,universalMatrix_det K⟩

variable {R : Type v} [CommRing R] [Algebra K R]

def polynomialEvaluation (M : Matrix Index Index R) : Polynomial K →ₐ[K] R :=
  MvPolynomial.aeval (fun ij => M ij.1 ij.2)

@[simp] theorem polynomialEvaluation_X (M : Matrix Index Index R) (i j : Index) :
    polynomialEvaluation K M (MvPolynomial.X (i,j)) = M i j := MvPolynomial.aeval_X _ _

theorem genericMatrix_evaluation (M : Matrix Index Index R) :
    (polynomialEvaluation K M).mapMatrix (genericMatrix K) = M := by
  ext i j
  exact polynomialEvaluation_X K M i j

theorem polynomialEvaluation_determinant (M : Matrix Index Index R) :
    polynomialEvaluation K M (determinant K) = M.det := by
  rw [determinant,AlgHom.map_det,genericMatrix_evaluation]

def evaluation (g : Matrix.SpecialLinearGroup Index R) : CoordinateRing K →ₐ[K] R :=
  Ideal.Quotient.liftₐ (relations K) (polynomialEvaluation K (g : Matrix Index Index R)) (by
    have h : relations K ≤ RingHom.ker (polynomialEvaluation K (g : Matrix Index Index R)) := by
      apply Ideal.span_le.mpr
      intro p hp
      obtain rfl := Set.mem_singleton_iff.mp hp
      change polynomialEvaluation K (g : Matrix Index Index R) (relation K) = 0
      rw [relation,map_sub,map_one,polynomialEvaluation_determinant,g.property,sub_self]
    intro p hp
    exact h hp)

@[simp] theorem evaluation_coordinate (g : Matrix.SpecialLinearGroup Index R) (i j : Index) :
    evaluation K g (coordinate K i j) = (g : Matrix Index Index R) i j := by
  change (Ideal.Quotient.liftₐ (relations K) _ _) (Ideal.Quotient.mk (relations K) _) = _
  rw [Ideal.Quotient.liftₐ_apply,Ideal.Quotient.lift_mk]
  exact polynomialEvaluation_X K _ i j

def matrixOfHom (f : CoordinateRing K →ₐ[K] R) : Matrix.SpecialLinearGroup Index R :=
  ⟨f.mapMatrix (universalMatrix K),by rw [← AlgHom.map_det,universalMatrix_det,map_one]⟩

@[simp] theorem matrixOfHom_apply (f : CoordinateRing K →ₐ[K] R) (i j : Index) :
    (matrixOfHom K f : Matrix Index Index R) i j = f (coordinate K i j) := rfl

/-- The displayed actual quotient represents literal special-linear matrices. -/
def homEquiv : (CoordinateRing K →ₐ[K] R) ≃ Matrix.SpecialLinearGroup Index R where
  toFun := matrixOfHom K
  invFun := evaluation K
  left_inv f := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro ij
    change evaluation K (matrixOfHom K f) (coordinate K ij.1 ij.2) = f (coordinate K ij.1 ij.2)
    rw [evaluation_coordinate,matrixOfHom_apply]
  right_inv g := by
    apply Subtype.ext
    ext i j
    exact evaluation_coordinate K g i j


/-- The actual point equivalence is natural for every K-algebra homomorphism. -/
theorem homEquiv_comp {S : Type w} [CommRing S] [Algebra K S]
    (f : CoordinateRing K →ₐ[K] R) (ρ : R →ₐ[K] S) :
    homEquiv K (ρ.comp f) = Matrix.SpecialLinearGroup.map ρ.toRingHom (homEquiv K f) := by
  apply Subtype.ext
  rfl

instance coordinateRing_finiteType : Algebra.FiniteType K (CoordinateRing K) := by infer_instance

abbrev GLRing := Localization.Away (determinant K)
def polynomialToGL : Polynomial K →ₐ[K] GLRing K :=
  IsScalarTower.toAlgHom K (Polynomial K) (GLRing K)
def localizedMatrix : Matrix Index Index (GLRing K) :=
  (polynomialToGL K).mapMatrix (genericMatrix K)
def inverseDet : GLRing K := IsLocalization.Away.invSelf (determinant K)

theorem localizedMatrix_det : (localizedMatrix K).det = polynomialToGL K (determinant K) :=
  ((polynomialToGL K).map_det (genericMatrix K)).symm

theorem inverseDet_mul : inverseDet K*polynomialToGL K (determinant K) = 1 := by
  rw [mul_comm]
  exact IsLocalization.Away.mul_invSelf (determinant K)

def normalizedMatrix : Matrix Index Index (GLRing K) :=
  (localizedMatrix K).updateRow 0 (inverseDet K • localizedMatrix K 0)

theorem normalizedMatrix_det : (normalizedMatrix K).det = 1 := by
  rw [normalizedMatrix,Matrix.det_updateRow_smul,Matrix.updateRow_eq_self,localizedMatrix_det]
  exact inverseDet_mul K

def normalizedPoint : Matrix.SpecialLinearGroup Index (GLRing K) :=
  ⟨normalizedMatrix K,normalizedMatrix_det K⟩

theorem quotientMap_determinant_one : quotientMap K (determinant K) = 1 :=
  (quotientMap_determinant K).trans (universalMatrix_det K)

theorem determinant_quotient_unit : IsUnit (quotientMap K (determinant K)) := by
  rw [quotientMap_determinant_one]
  exact isUnit_one

def specializeGL : GLRing K →ₐ[K] CoordinateRing K :=
  IsLocalization.Away.liftAlgHom (determinant K) (f := quotientMap K) (determinant_quotient_unit K)

@[simp] theorem specializeGL_polynomial (p : Polynomial K) :
    specializeGL K (polynomialToGL K p) = quotientMap K p :=
  IsLocalization.Away.lift_eq (S := GLRing K) (g := (quotientMap K).toRingHom)
    (determinant K) (determinant_quotient_unit K) p

theorem specializeGL_inverseDet : specializeGL K (inverseDet K) = 1 := by
  have h := congrArg (specializeGL K) (inverseDet_mul K)
  rw [map_mul,map_one,specializeGL_polynomial,quotientMap_determinant_one,mul_one] at h
  exact h

theorem specializeGL_localizedMatrix :
    (specializeGL K).mapMatrix (localizedMatrix K) = universalMatrix K := by
  ext i j
  exact specializeGL_polynomial K (MvPolynomial.X (i,j))

theorem specializeGL_normalizedMatrix :
    (specializeGL K).mapMatrix (normalizedMatrix K) = universalMatrix K := by
  have h := specializeGL_localizedMatrix K
  ext i j
  by_cases hi : i=0
  · subst i
    simpa [normalizedMatrix,specializeGL_inverseDet,map_mul] using congrFun (congrFun h 0) j
  · simpa [normalizedMatrix,hi] using congrFun (congrFun h i) j

/-- Normalize the first row of the generic invertible matrix. -/
def normalizationEmbedding : CoordinateRing K →ₐ[K] GLRing K := evaluation K (normalizedPoint K)

theorem specializeGL_comp_normalization :
    (specializeGL K).comp (normalizationEmbedding K) = AlgHom.id K (CoordinateRing K) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro ij
  change specializeGL K (evaluation K (normalizedPoint K) (coordinate K ij.1 ij.2)) =
    coordinate K ij.1 ij.2
  rw [evaluation_coordinate]
  exact congrFun (congrFun (specializeGL_normalizedMatrix K) ij.1) ij.2

theorem normalizationEmbedding_injective : Function.Injective (normalizationEmbedding K) := by
  have h : Function.LeftInverse (specializeGL K) (normalizationEmbedding K) := by
    intro a
    exact DFunLike.congr_fun (specializeGL_comp_normalization K) a
  exact h.injective

end Basic

section Domain

variable (K : Type u) [Field K]

theorem determinant_ne_zero : determinant K ≠ 0 := by
  intro h
  have he := polynomialEvaluation_determinant K (1 : Matrix Index Index K)
  rw [h,map_zero,Matrix.det_one] at he
  exact zero_ne_one he

instance glRing_isDomain : IsDomain (GLRing K) :=
  Localization.Away.isDomain (determinant_ne_zero K)

/-- The actual determinant-one quotient embeds in the actual polynomial localization. -/
instance coordinateRing_isDomain : IsDomain (CoordinateRing K) :=
  Function.Injective.isDomain (normalizationEmbedding K).toRingHom (normalizationEmbedding_injective K)

end Domain

end M9Native.SL3CoordinateRing
