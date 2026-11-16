module

public import M9StacksIntegration.Sp6GaussCellFunctor
public import M9StacksIntegration.LagrangianMatrixChart

/-!
# Coordinates representing the full Gauss cell

The two actual symmetric matrices use their six actual upper
triangular entries. The middle coefficient ring is the genuine
native GL3 coordinate ring. This is a polynomial ring in twelve
variables over the actual determinant localization for GL3.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Matrix AlgebraicGeometry

universe u

namespace M9Native.Sp6GaussCellCoordinates

open Sp6GaussBlockFactorization Sp6GaussCellFunctor
open LagrangianMatrixChart (SymmetricEntry symmetricIndex)

abbrev SymIndex := ULift.{u} SymmetricEntry
abbrev ExtraIndex := SymIndex.{u} ⊕ SymIndex.{u}
abbrev CoordinateRing : Type u :=
  MvPolynomial ExtraIndex.{u} (generalLinearCoordinateRing.{u} 3)

theorem card_symIndex : Fintype.card SymIndex.{u} = 6 := by
  simp only [Fintype.card_ulift, LagrangianMatrixChart.card_symmetricEntry]

theorem card_extraIndex : Fintype.card ExtraIndex.{u} = 12 := by
  simp only [Fintype.card_sum, card_symIndex]

variable (R : Type u) [CommRing R]

def symmetricCoordinatesEquiv : (SymIndex.{u} → R) ≃ Symmetric3 R where
  toFun v := ⟨fun i j => v ⟨symmetricIndex (i,j)⟩, by
    ext i j
    change v ⟨symmetricIndex (j,i)⟩ = v ⟨symmetricIndex (i,j)⟩
    rw [LagrangianMatrixChart.symmetricIndex_swap]⟩
  invFun M p := M.val p.down.val.1 p.down.val.2
  left_inv v := by
    funext p
    change v ⟨symmetricIndex p.down.val⟩ = v p
    rw [LagrangianMatrixChart.symmetricIndex_of_le]
  right_inv M := by
    apply Subtype.ext
    ext i j
    change M.val (symmetricIndex (i,j)).val.1 (symmetricIndex (i,j)).val.2 = M.val i j
    by_cases hij : i ≤ j
    · simp only [symmetricIndex, dite_eq_left hij]
    · have hm : M.val j i = M.val i j := congrFun (congrFun M.property i) j
      simpa only [symmetricIndex, dite_eq_right hij] using hm

def parametersOfHom (f : CoordinateRing.{u} →+* R) : Parameters R :=
  (symmetricCoordinatesEquiv R (fun i => f (MvPolynomial.X (Sum.inl i))),
    localizedPolynomialHomEquiv 3 R (f.comp MvPolynomial.C),
    symmetricCoordinatesEquiv R (fun i => f (MvPolynomial.X (Sum.inr i))))

def evaluation (p : Parameters R) : CoordinateRing.{u} →+* R :=
  MvPolynomial.eval₂Hom ((localizedPolynomialHomEquiv 3 R).symm p.2.1)
    (Sum.elim ((symmetricCoordinatesEquiv R).symm p.1)
      ((symmetricCoordinatesEquiv R).symm p.2.2))

/-- The actual parameter scheme represents exactly the two symmetric
matrices and the actual invertible middle matrix, over every ring. -/
def homEquiv : (CoordinateRing.{u} →+* R) ≃ Parameters R where
  toFun := parametersOfHom R
  invFun := evaluation R
  left_inv f := by
    apply MvPolynomial.ringHom_ext'
    · rw [evaluation, MvPolynomial.eval₂Hom_comp_C]
      exact (localizedPolynomialHomEquiv 3 R).symm_apply_apply _
    · intro i
      cases i with
      | inl i =>
        rw [evaluation, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
        change ((symmetricCoordinatesEquiv R).symm
          (symmetricCoordinatesEquiv R (fun j => f (MvPolynomial.X (Sum.inl j))))) i =
            f (MvPolynomial.X (Sum.inl i))
        exact congrFun ((symmetricCoordinatesEquiv R).symm_apply_apply _) i
      | inr i =>
        rw [evaluation, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
        change ((symmetricCoordinatesEquiv R).symm
          (symmetricCoordinatesEquiv R (fun j => f (MvPolynomial.X (Sum.inr j))))) i =
            f (MvPolynomial.X (Sum.inr i))
        exact congrFun ((symmetricCoordinatesEquiv R).symm_apply_apply _) i
  right_inv p := by
    apply Prod.ext
    · change symmetricCoordinatesEquiv R
        (fun i => evaluation R p (MvPolynomial.X (Sum.inl i))) = p.1
      have hx : (fun i => evaluation R p (MvPolynomial.X (Sum.inl i))) =
          (symmetricCoordinatesEquiv R).symm p.1 := by
        funext i
        simp only [evaluation, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, Sum.elim_inl]
      rw [hx, Equiv.apply_symm_apply]
    · apply Prod.ext
      · change localizedPolynomialHomEquiv 3 R ((evaluation R p).comp MvPolynomial.C) = p.2.1
        rw [evaluation, MvPolynomial.eval₂Hom_comp_C, Equiv.apply_symm_apply]
      · change symmetricCoordinatesEquiv R
          (fun i => evaluation R p (MvPolynomial.X (Sum.inr i))) = p.2.2
        have hx : (fun i => evaluation R p (MvPolynomial.X (Sum.inr i))) =
            (symmetricCoordinatesEquiv R).symm p.2.2 := by
          funext i
          simp only [evaluation, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, Sum.elim_inr]
        rw [hx, Equiv.apply_symm_apply]

variable {R} {S : Type u} [CommRing S]

/-- Naturality is over all coefficient rings, so no field-valued-point
or reducedness assumption enters the representing chart. -/
theorem homEquiv_comp (f : CoordinateRing.{u} →+* R) (ρ : R →+* S) :
    homEquiv S (ρ.comp f) = mapParameters ρ (homEquiv R f) := by
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · apply Prod.ext
    · exact localizedPolynomialHomEquiv_comp 3 (f.comp MvPolynomial.C) ρ
    · apply Subtype.ext
      rfl

end M9Native.Sp6GaussCellCoordinates

