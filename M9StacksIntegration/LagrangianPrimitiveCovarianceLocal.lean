module

public import M9StacksIntegration.LagrangianDeterminantActionMatrix
public import M9StacksIntegration.LagrangianPrimitiveRowAction

/-! The raw primitive matrix law in a genuine frame of an actual quotient
bundle.  All coefficients use the original projection matrix. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators

universe u

namespace M9Native.LagrangianPrimitiveCovarianceLocal

open LagrangianGrassmannian LagrangianMatrixChart LagrangianPluckerQuotient
open LagrangianDeterminantSections LagrangianSymplecticAction LagrangianTransitivity
open PrimitiveRingRepresentation PrimitiveRingMatrices LagrangianPrimitiveRowAction
open LagrangianSigmaInvariance

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

variable (K : Type u) [Field K] [CharZero K]

omit [CharZero K] in
/-- Scalar extension preserves the literal transpose primitive matrix. -/
theorem rawMatrix_scalar {R : Type u} [CommRing R] (κ : K →+* R)
    (g : Matrix.symplecticGroup (Fin 3) K) :
    matrix14 R K κ (transposeSymplectic R (mapSymplectic K κ g)) =
      (matrix14 K K (RingHom.id K) (transposeSymplectic K g)).map κ := by
  have ht : transposeSymplectic R (mapSymplectic K κ g) =
      mapSymplectic K κ (transposeSymplectic K g) := by
    apply Subtype.ext
    rfl
  rw [ht]
  simpa only [RingHom.comp_id] using
    matrix14_map K K (RingHom.id K) κ (transposeSymplectic K g)

/-- The actual primitive determinant sections obey the original matrix
law in every actual quotient frame whose rows are isotropic. -/
theorem primitiveSection_precomp_framed {T : Scheme.{u}}
    (b : T ⟶ Spec (.of K)) {Q : T.Modules} (q : freeOn T 6 ⟶ Q)
    (e : Q ≅ freeOn T 3)
    (hq : AnnihilatesSigma T (q ≫ e.hom))
    (g : Matrix.symplecticGroup (Fin 3) K) (j : Fin 14) :
    primitiveSection T K (scalarMap K b) ((constantFreeIso K b g).hom ≫ q) j =
      ∑ a : Fin 14,
        scalarMap K b (matrix14 K K (RingHom.id K) (transposeSymplectic K g) j a) •
          primitiveSection T K (scalarMap K b) q a := by
  let E := (Scheme.Modules.exteriorPowerFunctor T 3).mapIso e
  apply (ConcreteCategory.bijective_of_isIso (E.hom.app ⊤)).injective
  change (Scheme.Modules.exteriorPowerMap e.hom 3).app ⊤ _ =
    (Scheme.Modules.exteriorPowerMap e.hom 3).app ⊤ _
  simp only [map_sum, Scheme.Modules.Hom.app_smul]
  change (exteriorPowerMap T e.hom 3).app ⊤ _ = _
  simp only [← exteriorPowerMap_eq_native, primitiveSection_postcomp, Category.assoc]
  apply (freeDeterminantCoordinates T).injective
  simp only [map_sum, map_smul, primitiveSection_freeCoordinates, smul_eq_mul]
  rw [Stacks.FreeSheafMatrix.toMatrix_comp, constantFreeIso_matrix]
  have hr := rowFourteen_mul_symplectic Γ(T, ⊤) K (scalarMap K b)
    (Stacks.FreeSheafMatrix.toMatrix (q ≫ e.hom))
    (LagrangianPlucker.rows_isotropic_of_annihilatesSigma T (q ≫ e.hom) hq)
    (mapSymplectic K (scalarMap K b) g)
  rw [matrixSix_map, rawMatrix_scalar] at hr
  simpa only [constantMatrix, Matrix.mulVec, dotProduct, Matrix.map_apply] using congrFun hr j

end M9Native.LagrangianPrimitiveCovarianceLocal
