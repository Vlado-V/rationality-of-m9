module

public import M9StacksIntegration.ConicFramePolynomial

/-! The literal polynomial conic-frame quotient commutes with actual
coefficient-ring maps. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9Native.ConicFrame

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)

theorem symCoordinates_map (A : Mat3 R) (i : Fin 6) :
    symCoordinates (A.map φ) i = φ (symCoordinates A i) := by
  fin_cases i <;> rfl

theorem symMatrix_map (x : Fin 6 → R) :
    (symMatrix x).map φ = symMatrix (fun i => φ (x i)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem congruence_map (F : Mat3 R) : (congruence F).map φ = congruence (F.map φ) := by
  ext i j
  change φ (symCoordinates (F * symMatrix (Pi.single j 1) * F.transpose) i) = _
  rw [← symCoordinates_map,Matrix.map_mul,Matrix.map_mul,symMatrix_map]
  have hs : (fun i : Fin 6 => φ ((Pi.single j (1 : R) : Fin 6 → R) i)) =
      (Pi.single j (1 : S) : Fin 6 → S) := by
    funext i
    classical
    simp [Pi.single_apply]
  rw [hs]
  rfl

theorem standardQuotient_map :
    (standardQuotient : Matrix (Fin 2) (Fin 6) R).map φ = standardQuotient := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [standardQuotient]

theorem quotientMatrix_map (F : Mat3 R) :
    (quotientMatrix F).map φ = quotientMatrix (F.map φ) := by
  rw [quotientMatrix,Matrix.map_mul,standardQuotient_map,congruence_map]
  have ha : F.adjugate.map φ = (F.map φ).adjugate := by
    simpa only [RingHom.mapMatrix_apply] using φ.map_adjugate F
  rw [ha]
  rfl

end M9Native.ConicFrame
