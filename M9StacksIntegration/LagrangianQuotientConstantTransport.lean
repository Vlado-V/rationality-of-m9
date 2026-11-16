module

public import M9StacksIntegration.LagrangianQuotientExteriorEvaluation

/-!
# Actual constant symplectic transport of quotient exterior evaluation

The actual sheaf automorphism with its native scalar matrix acts on the
original six cohomology sections by the genuine field linear equivalence.
Its actual exterior map is surjective, so the full degree-three evaluation
image is unchanged. No action-identification premise is introduced.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators

universe u

namespace M9Native.LagrangianQuotientConstantTransport

open LagrangianField LagrangianGrassmannian LagrangianMatrixChart
open LagrangianSymplecticAction LagrangianTransitivity LagrangianSigmaInvariance
open LagrangianFreeMatrixPullback LagrangianQuotientExteriorEvaluation

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

variable {X : Scheme.{u}} (k : Type u) [Field k] (f : X ⟶ Spec (.of k))
  {Q : X.Modules} (q : freeOn X 6 ⟶ Q)

theorem scalarMap_eq_baseRingMap : scalarMap k f = ExteriorEvaluation.baseRingMap k f := by
  have happ : f.appLE ⊤ ⊤ (by simp) = f.appTop := by
    have h : X.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ by simp)).op =
        𝟙 Γ(X, ⊤) := by
      change X.presheaf.map (𝟙 (op (⊤ : X.Opens))) = _
      exact X.presheaf.map_id _
    rw [Scheme.Hom.appLE, h]
    exact Category.comp_id _
  unfold scalarMap ExteriorEvaluation.baseRingMap
  rw [happ]

theorem originalSectionMap_sections (v : Fin 6 → k) :
    (cohomologyOverFieldZeroLinearIso k f Q).hom (originalSectionMap k f q v) =
      ∑ i : Fin 6, ExteriorEvaluation.baseRingMap k f (v i) •
        q.app ⊤ (freeBasisSection X 6 i) := by
  have hscalar (a : k) (s : cohomologyOverField k f Q 0) :
      (cohomologyOverFieldZeroLinearIso k f Q).hom (a • s) =
        ExteriorEvaluation.baseRingMap k f a •
          (cohomologyOverFieldZeroLinearIso k f Q).hom s :=
    (cohomologyOverFieldZeroLinearIso k f Q).hom.hom.map_smul a s
  simp only [originalSectionMap, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply, map_sum, hscalar, originalSection_sections]

/-- The actual constant automorphism precomposes the literal sheaf quotient. -/
def transformedQuotient (g : Matrix.symplecticGroup (Fin 3) k) : freeOn X 6 ⟶ Q :=
  (constantFreeIso k f g).hom ≫ q

theorem originalSectionMap_transformed (g : Matrix.symplecticGroup (Fin 3) k) :
    originalSectionMap k f (transformedQuotient k f q g) =
      (originalSectionMap k f q).comp (symplecticEquiv k g).toLinearMap := by
  apply (Pi.basisFun k (Fin 6)).ext
  intro i
  simp only [Pi.basisFun_apply]
  change originalSectionMap k f (transformedQuotient k f q g) (basisVector k i) =
    ((originalSectionMap k f q).comp (symplecticEquiv k g).toLinearMap) (basisVector k i)
  rw [originalSectionMap_basis, LinearMap.comp_apply]
  change originalSection k f (transformedQuotient k f q g) i =
    originalSectionMap k f q ((matrixSix k g).mulVec (basisVector k i))
  apply (ConcreteCategory.bijective_of_isIso (cohomologyOverFieldZeroLinearIso k f Q).hom).injective
  rw [originalSection_sections, originalSectionMap_sections]
  change q.app ⊤ ((constantFreeIso k f g).hom.app ⊤ (freeBasisSection X 6 i)) = _
  have h := end_column_eq_sum X (constantFreeIso k f g).hom i
  change (constantFreeIso k f g).hom.app ⊤ (freeBasisSection X 6 i) =
    ∑ j : Fin 6, Stacks.FreeSheafMatrix.toMatrix (constantFreeIso k f g).hom j i •
      freeBasisSection X 6 j at h
  rw [h, map_sum]
  simp only [Scheme.Modules.Hom.app_smul, constantFreeIso_matrix, constantMatrix,
    Matrix.map_apply, scalarMap_eq_baseRingMap, basisVector, Matrix.mulVec_single_one,
    Matrix.col_apply]

theorem lambda_transformed (g : Matrix.symplecticGroup (Fin 3) k) (n : ℕ) :
    lambda k f (transformedQuotient k f q g) n =
      (lambda k f q n).comp (exteriorPower.map n (symplecticEquiv k g).toLinearMap) := by
  simp only [lambda, originalSectionMap_transformed, exteriorPower.map_comp,
    LinearMap.comp_assoc]

/-- Actual invertible constant source transport preserves the full original exterior image. -/
theorem range_lambda_transformed (g : Matrix.symplecticGroup (Fin 3) k) (n : ℕ) :
    LinearMap.range (lambda k f (transformedQuotient k f q g) n) =
      LinearMap.range (lambda k f q n) := by
  rw [lambda_transformed]
  apply Submodule.ext
  intro t
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨exteriorPower.map n (symplecticEquiv k g).toLinearMap w, rfl⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨v, hv⟩ := exteriorPower.map_surjective (n := n) (symplecticEquiv k g).surjective w
    exact ⟨v, by simp only [LinearMap.comp_apply, hv]⟩

theorem transformedQuotient_annihilates (g : Matrix.symplecticGroup (Fin 3) k)
    (hq : AnnihilatesSigma X q) : AnnihilatesSigma X (transformedQuotient k f q g) :=
  (annihilatesSigma_precomp_iff X q (mapSymplectic k (scalarMap k f) g)).mpr hq

/-- A genuine field-vector relation becomes the literal first-vector
relation of the actual transported quotient. -/
theorem transformed_first_section_zero (g : Matrix.symplecticGroup (Fin 3) k)
    (v : Fin 6 → k) (hg : symplecticEquiv k g (basisVector k 0) = v)
    (hv : originalSectionMap k f q v = 0) :
    (transformedQuotient k f q g).app ⊤ (freeBasisSection X 6 0) = 0 := by
  have h : originalSectionMap k f (transformedQuotient k f q g) (basisVector k 0) = 0 := by
    rw [originalSectionMap_transformed, LinearMap.comp_apply, LinearEquiv.coe_coe, hg, hv]
  have h' := congrArg (fun s => (cohomologyOverFieldZeroLinearIso k f Q).hom s) h
  simpa only [originalSectionMap_basis, originalSection_sections, map_zero] using h'

end M9Native.LagrangianQuotientConstantTransport
