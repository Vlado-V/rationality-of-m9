module

public import M9StacksIntegration.LagrangianUniversalSections
public import M9StacksIntegration.LagrangianFreeMatrixPullback
public import M9StacksIntegration.LagrangianCotangentFormula
public import M9StacksIntegration.SymplecticUnitWitness

/-! Original constant vectors have their original structural
coefficients in the actual free-six sheaf. Their symplectic pairing is
the actual structural image of the original field pairing. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.LagrangianConstantSymplectic

open LagrangianMatrixChart LagrangianUniversalSections LagrangianFreeMatrixPullback

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

theorem constantVector_coordinates (v : Fin 6 → k) :
    freeSectionCoordinates X 6 (constantVector k f v) =
      fun i => ExteriorEvaluation.baseRingMap k f (v i) := by
  classical
  funext i
  simp only [constantVector,map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,
    freeCoordinates_basis,smul_eq_mul]
  simp

theorem constantVector_pairing (v w : Fin 6 → k) :
    LagrangianCotangentFormula.symplecticPair
      (freeSectionCoordinates X 6 (constantVector k f v))
      (freeSectionCoordinates X 6 (constantVector k f w)) =
        ExteriorEvaluation.baseRingMap k f (LagrangianRing.omega k v w) := by
  rw [constantVector_coordinates,constantVector_coordinates]
  simp only [LagrangianCotangentFormula.symplecticPair,LagrangianRing.omega_apply,
    LagrangianRing.omegaValue,LagrangianRing.eIndex,LagrangianRing.fIndex,
    map_sum,map_sub,map_mul]

theorem exists_constant_pairing_one (v : Fin 6 → k) (hv : v ≠ 0) :
    ∃ w : Fin 6 → k, LagrangianCotangentFormula.symplecticPair
      (freeSectionCoordinates X 6 (constantVector k f v))
      (freeSectionCoordinates X 6 (constantVector k f w)) = (1 : Γ(X,⊤)) := by
  obtain ⟨w,hw⟩ := SymplecticUnitWitness.exists_pairing_one k v hv
  exact ⟨w,by rw [constantVector_pairing,hw,map_one]⟩

end M9Native.LagrangianConstantSymplectic
end
