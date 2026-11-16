module

public import M9.CayleyField
import Mathlib.Tactic

/-! Quadratic descent on the actual generic sixteen-variable matrix field.
The involution is constructed by the proved normalized Cayley coordinate
equivalence; its coefficient action and matrix inversion are then proved. -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9.CayleyFixedField

open Matrix M9.CayleyField M9.SemilinearInvolution

variable (L : Type*) [Field L] [CharZero L]

/-- The actual graph-field automorphism obtained by conjugating coefficient
descent through the normalized Cayley algebra equivalence. -/
def graphInvolution (σ : L ≃+* L) (θ : L) (hθ : θ ≠ 0) :
    CayleyField.Rational L ≃+* CayleyField.Rational L :=
  (normalizedAlgEquiv L θ hθ).symm.toRingEquiv |>.trans
    ((rationalInvolution Coordinate σ).trans (normalizedAlgEquiv L θ hθ).toRingEquiv)

theorem graphInvolution_apply (σ : L ≃+* L) (θ : L) (hθ : θ ≠ 0)
    (x : CayleyField.Rational L) :
    graphInvolution L σ θ hθ x =
      normalizedAlgEquiv L θ hθ
        (rationalInvolution Coordinate σ ((normalizedAlgEquiv L θ hθ).symm x)) := rfl

theorem graphInvolution_constant (σ : L ≃+* L) (θ : L) (hθ : θ ≠ 0) (a : L) :
    graphInvolution L σ θ hθ (algebraMap L (CayleyField.Rational L) a) =
      algebraMap L (CayleyField.Rational L) (σ a) := by
  rw [graphInvolution_apply, AlgEquiv.commutes,
    rationalInvolution_constant, AlgEquiv.commutes]

theorem graphInvolution_involutive (σ : L ≃+* L) (hσ : Function.Involutive σ)
    (θ : L) (hθ : θ ≠ 0) : Function.Involutive (graphInvolution L σ θ hθ) := by
  intro x
  rw [graphInvolution_apply, graphInvolution_apply, AlgEquiv.symm_apply_apply,
    rationalInvolution_involutive Coordinate σ hσ, AlgEquiv.apply_symm_apply]

theorem graphInvolution_normalized (σ : L ≃+* L) (θ : L) (hθ : θ ≠ 0)
    (ij : Coordinate) :
    graphInvolution L σ θ hθ (normalizedCoordinate L θ ij) = normalizedCoordinate L θ ij := by
  rw [← normalizedAlgEquiv_variable L θ hθ ij, graphInvolution_apply,
    AlgEquiv.symm_apply_apply]
  congr 1
  exact rationalInvolution_variable Coordinate σ ij

theorem graphInvolution_cayley_anti (σ : L ≃+* L) (θ : L) (hθ : θ ≠ 0)
    (hanti : σ θ = -θ) (ij : Coordinate) :
    graphInvolution L σ θ hθ (cayleyCoordinate L ij) = -cayleyCoordinate L ij := by
  have hθ' : algebraMap L (CayleyField.Rational L) θ ≠ 0 :=
    (map_ne_zero (algebraMap L (CayleyField.Rational L))).mpr hθ
  have hback : cayleyCoordinate L ij =
      algebraMap L (CayleyField.Rational L) θ * normalizedCoordinate L θ ij := by
    simp only [normalizedCoordinate, ← mul_assoc, mul_inv_cancel₀ hθ', one_mul]
  calc
    graphInvolution L σ θ hθ (cayleyCoordinate L ij) =
        graphInvolution L σ θ hθ
          (algebraMap L (CayleyField.Rational L) θ * normalizedCoordinate L θ ij) :=
      congrArg _ hback
    _ = -(algebraMap L (CayleyField.Rational L) θ) * normalizedCoordinate L θ ij := by
      rw [map_mul, graphInvolution_constant, hanti, map_neg, graphInvolution_normalized]
    _ = -cayleyCoordinate L ij := by rw [neg_mul, ← hback]

/-- The constructed automorphism has exactly the paper's matrix inversion
action on the original generic matrix, rather than an assumed substitute. -/
theorem graphInvolution_matrix (σ : L ≃+* L) (θ : L) (hθ : θ ≠ 0)
    (hanti : σ θ = -θ) :
    (graphInvolution L σ θ hθ).toRingHom.mapMatrix (genericMatrix L) =
      (genericMatrix L)⁻¹ := by
  let τ := graphInvolution L σ θ hθ
  have hplus := genericMatrix_add_one_det_ne_zero L
  have hX := genericMatrix_det_ne_zero L
  have hmapped : ((τ.toRingHom.mapMatrix (genericMatrix L)) + 1).det ≠ 0 := by
    have h : (τ.toRingHom.mapMatrix (genericMatrix L + 1)).det ≠ 0 := by
      rw [← τ.toRingHom.map_det]
      exact (map_ne_zero τ.toRingHom).mpr hplus
    simpa only [map_add, map_one] using h
  have hC : τ.toRingHom.mapMatrix (cayley (genericMatrix L)) = -cayley (genericMatrix L) := by
    ext i j
    exact graphInvolution_cayley_anti L σ θ hθ hanti (i,j)
  have hc : cayley (τ.toRingHom.mapMatrix (genericMatrix L)) = cayley ((genericMatrix L)⁻¹) := by
    rw [← map_cayley τ.toRingHom (genericMatrix L) hplus, hC, cayley_inv _ hX hplus]
  calc
    τ.toRingHom.mapMatrix (genericMatrix L) =
        inverseCayley (cayley (τ.toRingHom.mapMatrix (genericMatrix L))) :=
      (inverseCayley_cayley _ hmapped).symm
    _ = inverseCayley (cayley ((genericMatrix L)⁻¹)) := congrArg inverseCayley hc
    _ = (genericMatrix L)⁻¹ :=
      inverseCayley_cayley _ (inverse_add_one_det_ne_zero _ hX hplus)

omit [CharZero L] in
/-- Rational-field homomorphisms are determined by constants and the actual
generic matrix entries. -/
theorem rationalHom_ext {E : Type*} [Field E]
    (f g : CayleyField.Rational L →+* E)
    (hconst : ∀ a : L, f (algebraMap L (CayleyField.Rational L) a) =
      g (algebraMap L (CayleyField.Rational L) a))
    (hvar : ∀ ij : Coordinate, f (genericCoordinate L ij) = g (genericCoordinate L ij)) :
    f = g := by
  have hp : ∀ p : CayleyField.Polynomial L,
      f (algebraMap _ (CayleyField.Rational L) p) =
        g (algebraMap _ (CayleyField.Rational L) p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => exact hconst a
    | add p q hp hq => simp only [map_add,hp,hq]
    | mul_X p ij hp =>
      simpa only [map_mul, genericCoordinate, genericMatrix, Prod.mk.eta] using
        congrArg₂ (· * ·) hp (hvar ij)
  ext x
  obtain ⟨p,q,_,rfl⟩ := IsFractionRing.div_surjective (CayleyField.Polynomial L) x
  simp only [map_div₀, hp]

/-- The proved automorphism is the unique automorphism with the specified
coefficient action and matrix inversion. -/
theorem graphInvolution_unique (σ : L ≃+* L) (θ : L) (hθ : θ ≠ 0)
    (hanti : σ θ = -θ) (τ : CayleyField.Rational L ≃+* CayleyField.Rational L)
    (hc : ∀ a : L, τ (algebraMap L (CayleyField.Rational L) a) =
      algebraMap L (CayleyField.Rational L) (σ a))
    (hX : τ.toRingHom.mapMatrix (genericMatrix L) = (genericMatrix L)⁻¹) :
    τ = graphInvolution L σ θ hθ := by
  apply RingEquiv.toRingHom_injective
  apply rationalHom_ext L
  · intro a
    exact (hc a).trans (graphInvolution_constant L σ θ hθ a).symm
  · rintro ⟨i,j⟩
    have heq := hX.trans (graphInvolution_matrix L σ θ hθ hanti).symm
    exact congrFun (congrFun heq i) j

/-- Restrict the proved normalized coordinate equivalence to the actual
equalizer subfields of the conjugate automorphisms. -/
def fixedGraphRingEquiv (σ : L ≃+* L) (θ : L) (hθ : θ ≠ 0) :
    fixedField (rationalInvolution Coordinate σ) ≃+*
      fixedField (graphInvolution L σ θ hθ) where
  toFun x := ⟨normalizedAlgEquiv L θ hθ x.val,by
    change normalizedAlgEquiv L θ hθ
      (rationalInvolution Coordinate σ
        ((normalizedAlgEquiv L θ hθ).symm (normalizedAlgEquiv L θ hθ x.val))) =
          normalizedAlgEquiv L θ hθ x.val
    rw [AlgEquiv.symm_apply_apply]
    have hx : rationalInvolution Coordinate σ x.val = x.val := x.property
    exact congrArg (normalizedAlgEquiv L θ hθ) hx⟩
  invFun y := ⟨(normalizedAlgEquiv L θ hθ).symm y.val,by
    change rationalInvolution Coordinate σ ((normalizedAlgEquiv L θ hθ).symm y.val) =
      (normalizedAlgEquiv L θ hθ).symm y.val
    apply (normalizedAlgEquiv L θ hθ).injective
    rw [AlgEquiv.apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext (AlgEquiv.symm_apply_apply _ _)
  right_inv y := Subtype.ext (AlgEquiv.apply_symm_apply _ _)
  map_mul' x y := Subtype.ext (map_mul (normalizedAlgEquiv L θ hθ) _ _)
  map_add' x y := Subtype.ext (map_add (normalizedAlgEquiv L θ hθ) _ _)

/-- The fixed coefficient field embeds as constants in the actual graph
invariant field. -/
def graphFixedBaseEmbedding (σ : L ≃+* L) (θ : L) (hθ : θ ≠ 0) :
    fixedField σ →+* fixedField (graphInvolution L σ θ hθ) where
  toFun a := ⟨algebraMap L (CayleyField.Rational L) (a : L),by
    change graphInvolution L σ θ hθ (algebraMap L (CayleyField.Rational L) (a : L)) = _
    rw [graphInvolution_constant, apply_fixed]
    rfl⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_mul' a b := Subtype.ext (map_mul _ _ _)

instance graphFixedAlgebra (σ : L ≃+* L) (θ : L) (hθ : θ ≠ 0) :
    Algebra (fixedField σ) (fixedField (graphInvolution L σ θ hθ)) :=
  (graphFixedBaseEmbedding L σ θ hθ).toAlgebra

def fixedGraphAlgEquiv (σ : L ≃+* L) (θ : L) (hθ : θ ≠ 0) :
    fixedField (rationalInvolution Coordinate σ) ≃ₐ[fixedField σ]
      fixedField (graphInvolution L σ θ hθ) where
  __ := fixedGraphRingEquiv L σ θ hθ
  commutes' a := by
    apply Subtype.ext
    change normalizedAlgEquiv L θ hθ (algebraMap L (CayleyField.Rational L) (a : L)) =
      algebraMap L (CayleyField.Rational L) (a : L)
    exact AlgEquiv.commutes _ _

/-- Rationality in sixteen variables of the actual graph invariant field,
over its actual fixed coefficient field. No rationality premise is used. -/
def fixedGraphRationalAlgEquiv (σ : L ≃+* L) (hσ : Function.Involutive σ)
    (θ : L) (hθ : θ ≠ 0) :
    CayleyField.Rational (fixedField σ) ≃ₐ[fixedField σ]
      fixedField (graphInvolution L σ θ hθ) :=
  (fixedRationalAlgEquiv Coordinate σ hσ).trans (fixedGraphAlgEquiv L σ θ hθ)

theorem fixedGraphRationalAlgEquiv_variable (σ : L ≃+* L) (hσ : Function.Involutive σ)
    (θ : L) (hθ : θ ≠ 0) (ij : Coordinate) :
    (fixedGraphRationalAlgEquiv L σ hσ θ hθ (genericCoordinate (fixedField σ) ij) :
      CayleyField.Rational L) = normalizedCoordinate L θ ij := by
  change normalizedAlgEquiv L θ hθ
    (rationalInclude Coordinate σ
      (algebraMap (MvPolynomial Coordinate (fixedField σ))
        (CayleyField.Rational (fixedField σ)) (MvPolynomial.X ij))) = _
  rw [rationalInclude_polynomial]
  simp only [polynomialInclude, MvPolynomial.map_X]
  exact normalizedAlgEquiv_variable L θ hθ ij

/-- Every nontrivial coefficient involution yields the asserted actual
inversion-field action and its rational fixed field, with theta constructed
from that involution rather than assumed to exist. -/
theorem exists_inversion_fixed_rational (σ : L ≃+* L) (hσ : Function.Involutive σ)
    (hne : σ ≠ RingEquiv.refl L) :
    ∃ (θ : L) (hθ : θ ≠ 0),
      σ θ = -θ ∧
      (graphInvolution L σ θ hθ).toRingHom.mapMatrix (genericMatrix L) =
        (genericMatrix L)⁻¹ ∧
      Nonempty (CayleyField.Rational (fixedField σ) ≃ₐ[fixedField σ]
        fixedField (graphInvolution L σ θ hθ)) := by
  obtain ⟨b,hθ,hanti⟩ := exists_theta σ hσ hne
  exact ⟨theta σ b,hθ,hanti,graphInvolution_matrix L σ _ hθ hanti,
    ⟨fixedGraphRationalAlgEquiv L σ hσ _ hθ⟩⟩

end M9.CayleyFixedField
