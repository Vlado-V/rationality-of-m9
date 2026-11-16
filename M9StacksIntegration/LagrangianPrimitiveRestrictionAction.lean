module

public import M9StacksIntegration.LagrangianPrimitiveSectionCovariance
public import M9StacksIntegration.LagrangianPrimitiveRestriction

/-!
# Actual primitive restriction under the native LG action

The genuine determinant-line action preserves each original primitive
section by the proved raw fourteen-matrix transpose formula. Summing with
the original coefficients gives actual zero and kernel transport for the
original primitive restriction map on every test scheme. No preservation
of H0, polarization, or parameter orbit is an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Module Matrix
open scoped BigOperators Matrix

universe u
namespace M9Native.LagrangianPrimitiveRestrictionAction

open LagrangianGrassmannian LagrangianPrimitiveRestriction LagrangianSymplecticAction
open LagrangianPrimitiveSectionCovariance LagrangianSigmaInvariance PrimitiveRingMatrices

/-- Finite scalar combinations retain the literal transpose of the
original coefficient matrix. -/
theorem combination_transpose {K R V : Type*} [CommRing K] [CommRing R]
    [AddCommGroup V] [Module R V] {m n : ℕ}
    (κ : K →+* R) (B : Matrix (Fin m) (Fin n) K) (v : Fin m → K) (s : Fin n → V) :
    (∑ j : Fin m, κ (v j) • (∑ a : Fin n, κ (B j a) • s a)) =
      ∑ a : Fin n, κ ((B.transpose *ᵥ v) a) • s a := by
  simp only [Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, map_sum, map_mul, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

variable {X : Scheme.{u}} (K : Type u) [Field K] [CharZero K]
  (f : X ⟶ Spec (.of K)) (l : X ⟶ space K)
  (hl : l ≫ projection K = f) (g : Matrix.symplecticGroup (Fin 3) K)

/-- The raw primitive matrix relevant to the native quotient LG action
is the actual third exterior action of the transpose symplectic matrix. -/
abbrev actionMatrix : Matrix (Fin 14) (Fin 14) K :=
  matrix14 K K (RingHom.id K) (transposeSymplectic K g)

set_option maxHeartbeats 1200000 in
include hl in
/-- The actual line-action isomorphism sends the original acted
restriction to the original restriction of the exact transpose coefficient
vector, over the SAME scheme and original scalar field. -/
theorem restriction_sections (v : Fin 14 → K) :
    (LagrangianDeterminantAction.determinantActionIso K l g).hom.app ⊤
      ((cohomologyOverFieldZeroLinearIso K f (restrictedLine K (l ≫ action K g))).hom
        (primitiveRestriction K f (l ≫ action K g) v)) =
      (cohomologyOverFieldZeroLinearIso K f (restrictedLine K l)).hom
        (primitiveRestriction K f l ((actionMatrix K g).transpose *ᵥ v)) := by
  have hc (j : Fin 14) :
      (LagrangianDeterminantAction.determinantActionIso K l g).hom.app ⊤
        (restrictedSection K (l ≫ action K g) j) =
      ∑ a : Fin 14, LagrangianPlucker.coefficientMap K l (actionMatrix K g j a) •
        restrictedSection K l a :=
    determinantActionIso_primitive_covariance K l g j
  rw [primitiveRestriction_sections, primitiveRestriction_sections, map_sum]
  simp only [Scheme.Modules.Hom.app_smul, hc,
    LagrangianUniversalSections.coefficients K f l hl]
  exact combination_transpose (ExteriorEvaluation.baseRingMap K f) (actionMatrix K g) v
    (restrictedSection K l)

include hl in
/-- Vanishing is detected through actual isomorphisms, not assumed
compatibility of the original H0 spaces. -/
theorem restriction_zero_iff (v : Fin 14 → K) :
    primitiveRestriction K f (l ≫ action K g) v = 0 ↔
      primitiveRestriction K f l ((actionMatrix K g).transpose *ᵥ v) = 0 := by
  have ha := (ConcreteCategory.bijective_of_isIso
    (cohomologyOverFieldZeroLinearIso K f (restrictedLine K (l ≫ action K g))).hom).injective
  have hb := (ConcreteCategory.bijective_of_isIso
    ((LagrangianDeterminantAction.determinantActionIso K l g).hom.app ⊤)).injective
  have hc := (ConcreteCategory.bijective_of_isIso
    (cohomologyOverFieldZeroLinearIso K f (restrictedLine K l)).hom).injective
  constructor
  · intro h
    have hz : (cohomologyOverFieldZeroLinearIso K f (restrictedLine K l)).hom
        (primitiveRestriction K f l ((actionMatrix K g).transpose *ᵥ v)) = 0 := by
      rw [← restriction_sections K f l hl g v, h, map_zero, map_zero]
    exact (map_eq_zero_iff _ hc).mp hz
  · intro h
    have hz : (LagrangianDeterminantAction.determinantActionIso K l g).hom.app ⊤
        ((cohomologyOverFieldZeroLinearIso K f (restrictedLine K (l ≫ action K g))).hom
          (primitiveRestriction K f (l ≫ action K g) v)) = 0 := by
      rw [restriction_sections K f l hl g v, h, map_zero]
    exact (map_eq_zero_iff _ ha).mp ((map_eq_zero_iff _ hb).mp hz)

include hl in
/-- The exact original kernel is transported by the literal original
raw matrix transpose; no coordinate or kernel-transport premise is added. -/
theorem restriction_kernel :
    LinearMap.ker (primitiveRestriction K f (l ≫ action K g)) =
      LinearMap.ker ((primitiveRestriction K f l).comp (actionMatrix K g).transpose.mulVecLin) := by
  ext v
  exact restriction_zero_iff K f l hl g v

end M9Native.LagrangianPrimitiveRestrictionAction
