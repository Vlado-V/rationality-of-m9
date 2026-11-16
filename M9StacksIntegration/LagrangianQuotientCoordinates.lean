module

public import M9StacksIntegration.LagrangianCotangentMap
public import StacksFrontier.AlgebraicGeometry.Reflexive.DualMap

/-! The intrinsic coefficient formula under an actual change of quotient frame. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators TensorProduct

universe u

namespace M9Native.LagrangianQuotientCoordinates

open LagrangianGrassmannian LagrangianMatrixChart LagrangianDualCoefficients
open LagrangianCotangentMap LagrangianLocalPairing LagrangianCotangentFormula
open Stacks.AlgebraicGeometry.ReflexiveModules

variable {X S : Scheme.{u}} {Q Q' : X.Modules}

/-- The quotient's actual coefficient sections transform by the actual
morphism of quotient bundles, on every open. -/
theorem quotientVector_comp (q : freeOn X 6 ⟶ Q) (φ : Q ⟶ Q')
    (U : X.Opens) (j : Fin 6) :
    quotientVector (q ≫ φ) U j=φ.app U (quotientVector q U j) := by
  unfold quotientVector
  exact (ConcreteCategory.congr_hom
    (φ.val.naturality (homOfLE (show U≤⊤ from le_top)).op)
      (q.app ⊤ (freeVector X j))).symm

/-- Dual evaluation is compatible with the original quotient map,
without choosing a basis or assuming an evaluation formula. -/
theorem coefficientMap_comp (q : freeOn X 6 ⟶ Q) (φ : Q ⟶ Q')
    (U : X.Opens) (α : Γ(dualSheaf Q',U)) :
    coefficientMap (q ≫ φ) U α=coefficientMap q U ((dualMap φ).app U α) := by
  funext j
  change evalAt Q' α (quotientVector (q ≫ φ) U j)=
    evalAt Q ((dualMap φ).app U α) (quotientVector q U j)
  rw [quotientVector_comp]
  exact (dualPairing_dualMap φ α (Over.mk (𝟙 U)) (quotientVector q U j)).symm

/-- The actual local intrinsic bilinear form is natural under every
actual morphism of quotient bundles. -/
theorem localPairing_comp (p : X ⟶ S) (q : freeOn X 6 ⟶ Q)
    (hq : AnnihilatesSigma X q) (φ : Q ⟶ Q')
    (hφ : AnnihilatesSigma X (q ≫ φ)) (U : X.Opens)
    (α β : Γ(dualSheaf Q',U)) :
    localPairing p (q ≫ φ) hφ U α β=
      localPairing p q hq U ((dualMap φ).app U α) ((dualMap φ).app U β) := by
  change differentialPair (localDerivation p U) (coefficientMap (q ≫ φ) U) α β=
    differentialPair (localDerivation p U) (coefficientMap q U)
      ((dualMap φ).app U α) ((dualMap φ).app U β)
  simp only [differentialPair,coefficientMap_comp]

end M9Native.LagrangianQuotientCoordinates
