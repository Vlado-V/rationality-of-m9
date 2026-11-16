module

public import M9StacksIntegration.LagrangianFieldJetCoefficients
public import M9StacksIntegration.DeterminantRankOneDifferential

/-!
# Actual field-point cotangent specialization of a determinant

The actual native point derivative, in the genuine pullback cotangent
sections, satisfies Leibniz with the actual point-value ring map. It is
therefore an actual integer-linear derivation. Its determinant value
vanishes at literal matrix rank at most one, without a supplied linear
specialization, scalar formula, or differential-comparison premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Module

universe u

namespace M9Native.FieldPointDeterminantDifferential

open LagrangianFieldJetCoefficients

variable (K : Type u) [Field K] {X : Scheme.{u}}
  (b : X ⟶ Spec (.of K)) (z : Spec (.of K) ⟶ X)

/-- Arbitrary actual global coefficients specialize through the actual point-value ring map. -/
theorem pullback_smul_pointValue (a : Γ(X,⊤))
    (m : Γ(Scheme.Hom.relativeDifferentials b,⊤)) :
    pullbackGlobalSections z (Scheme.Hom.relativeDifferentials b) (a • m) =
      pointValue K z a • (show Cotangent K b z from
        pullbackGlobalSections z (Scheme.Hom.relativeDifferentials b) m) := by
  rw [SectionsEqualizer.pullbackGlobalSections_smul]
  have h : z.appTop a = (Scheme.ΓSpecIso (.of K)).inv (pointValue K z a) :=
    ((Scheme.ΓSpecIso (.of K)).hom_inv_id_apply (z.appTop a)).symm
  rw [h]
  rfl

/-- The genuine section-ring action through the actual point-value map. -/
@[instance_reducible]
def sectionModule : Module Γ(X,⊤) (Cotangent K b z) :=
  Module.compHom (Cotangent K b z) (pointValue K z)

/-- The actual cotangent-valued point derivative, as a literal integer-linear derivation. -/
def pointDerivation :
    letI := sectionModule K b z
    Derivation ℤ Γ(X,⊤) (Cotangent K b z) := by
  letI := sectionModule K b z
  apply Derivation.mk' (pointDerivative K b z).toIntLinearMap
  intro a c
  change pointDerivative K b z (a*c) =
    pointValue K z a • pointDerivative K b z c +
      pointValue K z c • pointDerivative K b z a
  rw [pointDerivative_apply, (Scheme.Hom.universalRelativeDerivation b).d_mul,
    map_add, pullback_smul_pointValue, pullback_smul_pointValue]
  rfl

theorem pointDerivation_apply (a : Γ(X,⊤)) :
    letI := sectionModule K b z
    pointDerivation K b z a = pointDerivative K b z a := rfl

/-- Rank-one actual evaluated matrices have zero actual native cotangent determinant derivative. -/
theorem pointDerivative_det_eq_zero_of_rank_le_one
    (A : Matrix (Fin 3) (Fin 3) Γ(X,⊤))
    (hr : (A.map (pointValue K z)).rank ≤ 1) :
    pointDerivative K b z A.det = 0 := by
  letI : Algebra Γ(X,⊤) K := (pointValue K z).toAlgebra
  letI := sectionModule K b z
  letI : IsScalarTower Γ(X,⊤) K (Cotangent K b z) :=
    ⟨fun r a m => mul_smul (pointValue K z r) a m⟩
  exact DeterminantRankOneDifferential.derivation_det_eq_zero_of_rank_map_le_one
    (pointDerivation K b z) A hr

/-- Thus a nonzero actual point derivative forces actual evaluated matrix rank at least two. -/
theorem two_le_rank_of_pointDerivative_det_ne_zero
    (A : Matrix (Fin 3) (Fin 3) Γ(X,⊤))
    (hd : pointDerivative K b z A.det ≠ 0) :
    2 ≤ (A.map (pointValue K z)).rank := by
  by_contra hn
  exact hd (pointDerivative_det_eq_zero_of_rank_le_one K b z A (by omega))

end M9Native.FieldPointDeterminantDifferential
