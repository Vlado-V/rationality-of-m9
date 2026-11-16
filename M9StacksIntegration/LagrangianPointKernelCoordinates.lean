module

public import M9StacksIntegration.LagrangianPluckerDuality
public import M9StacksIntegration.GrassmannianExteriorFieldCoordinates
public import M9StacksIntegration.LagrangianIncidenceFieldPoints
public import M9StacksIntegration.LagrangianPluckerGeneration
public import M9StacksIntegration.MukaiFourCircuitBasic

/-! Original field-point quotient charts, actual kernel frames, and the
fixed symplectic transformation of their full third-exterior volumes.
Every chart, pivot, isotropy equation and frame is derived from the
original LG point. No matrix/point or kernel-plane identification is input. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Matrix
open scoped BigOperators
universe u

namespace M9Native.LagrangianPointKernelCoordinates
open LagrangianGrassmannian LagrangianPluckerQuotient
open GrassmannianExteriorFieldCoordinates LagrangianPluckerDuality

variable (K : Type u) [Field K]

structure PointChart (p : Spec (.of K) ⟶ space K) where
  index : Fin 3 ↪ Fin 6
  map : Spec (.of K) ⟶ fieldChart index
  triangle : (p ≫ inclusion K) ≫ pullback.snd _ _ = map ≫ Grassmannian.chart 3 6 index

theorem nonempty_pointChart (p : Spec (.of K) ⟶ space K) : Nonempty (PointChart K p) := by
  obtain ⟨ι,g,hg⟩ := LagrangianIncidenceFieldPoints.exists_integralChart_factor K
    ((p ≫ inclusion K) ≫ pullback.snd _ _)
  exact ⟨⟨ι,g,hg⟩⟩

def pointChart (p : Spec (.of K) ⟶ space K) : PointChart K p :=
  Classical.choice (nonempty_pointChart K p)

def matrix (p : Spec (.of K) ⟶ space K) : Matrix (Fin 3) (Fin 6) K :=
  matrixOnField K (pointChart K p).index (pointChart K p).map

theorem matrix_pivots (p : Spec (.of K) ⟶ space K) :
    (matrix K p).submatrix id (pointChart K p).index = 1 :=
  matrixOnField_pivots K _ _

theorem matrix_surjective (p : Spec (.of K) ⟶ space K) :
    Function.Surjective (matrix K p).mulVec :=
  LagrangianTransitivity.matrix_surjective_of_pivots K _ _ (matrix_pivots K p)

theorem matrix_rows_independent (p : Spec (.of K) ⟶ space K) :
    LinearIndependent K (matrix K p) :=
  matrixOnField_rows_independent K _ _

theorem matrix_rows_isotropic (p : Spec (.of K) ⟶ space K) (i j : Fin 3) :
    LagrangianRing.omega K (matrix K p i) (matrix K p j) = 0 := by
  let ρ := (Scheme.ΓSpecIso (.of K)).hom.hom
  have h := congrArg ρ (LagrangianPlucker.chart_rows_isotropic K p
    (pointChart K p).index (pointChart K p).map (pointChart K p).triangle i j)
  simpa only [matrix, matrixOnField, ← Grassmannian.toMatrix_chartQuotientMap,
    LagrangianRing.omega_apply, LagrangianRing.omegaValue, map_sum, map_sub, map_mul,
    map_zero, Matrix.map_apply] using h

def kernelRows (p : Spec (.of K) ⟶ space K) : Fin 3 → (Fin 6 → K) :=
  kernelPartner K (matrix K p)

theorem kernelRows_independent (p : Spec (.of K) ⟶ space K) :
    LinearIndependent K (kernelRows K p) := by
  exact (matrix_rows_independent K p).map'
    (symplecticDualityEquiv K).toLinearMap
    (LinearMap.ker_eq_bot.mpr (symplecticDualityEquiv K).injective)

theorem kernelRows_mem_kernel (p : Spec (.of K) ⟶ space K) (i : Fin 3) :
    kernelRows K p i ∈ LinearMap.ker (matrix K p).mulVecLin :=
  kernelPartner_mem K _ (matrix_rows_isotropic K p) i

theorem kernelRows_span_le_kernel (p : Spec (.of K) ⟶ space K) :
    Submodule.span K (Set.range (kernelRows K p)) ≤ LinearMap.ker (matrix K p).mulVecLin := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact kernelRows_mem_kernel K p i

theorem matrix_kernel_finrank (p : Spec (.of K) ⟶ space K) :
    finrank K (LinearMap.ker (matrix K p).mulVecLin) = 3 := by
  have h := (matrix K p).mulVecLin.finrank_range_add_finrank_ker
  have hr : LinearMap.range (matrix K p).mulVecLin = ⊤ :=
    LinearMap.range_eq_top.mpr (matrix_surjective K p)
  rw [hr] at h
  simp only [finrank_top, Module.finrank_pi, Fintype.card_fin] at h
  omega

theorem kernelRows_span_eq_kernel (p : Spec (.of K) ⟶ space K) :
    Submodule.span K (Set.range (kernelRows K p)) = LinearMap.ker (matrix K p).mulVecLin := by
  apply Submodule.eq_of_le_of_finrank_eq (kernelRows_span_le_kernel K p)
  rw [finrank_span_eq_card (kernelRows_independent K p), matrix_kernel_finrank K p]
  rfl

def rowVolume (p : Spec (.of K) ⟶ space K) : ⋀[K]^3 (Fin 6 → K) :=
  exteriorPower.ιMulti K 3 (matrix K p)

def kernelVolume (p : Spec (.of K) ⟶ space K) : ⋀[K]^3 (Fin 6 → K) :=
  exteriorPower.ιMulti K 3 (kernelRows K p)

theorem kernelVolume_ne_zero (p : Spec (.of K) ⟶ space K) : kernelVolume K p ≠ 0 :=
  MukaiFourCircuit.ιMulti_ne_zero K _ (kernelRows_independent K p)

theorem rowVolume_to_kernelVolume (p : Spec (.of K) ⟶ space K) :
    exteriorPower.map 3 (symplecticDuality K) (rowVolume K p) = kernelVolume K p := by
  rw [rowVolume, exteriorPower.map_apply_ιMulti]
  rfl

theorem exterior_symplecticDuality_injective :
    Function.Injective (exteriorPower.map 3 (symplecticDuality K)) :=
  exteriorPower.map_injective_field (symplecticDualityEquiv K).injective

section CoefficientComparison
variable [CharZero K]

theorem rowTwenty_map {R S : Type u} [CommRing R] [CommRing S]
    (ρ : R →+* S) (M : Matrix (Fin 3) (Fin 6) R) :
    (fun i => ρ (LagrangianRing.rowTwenty R M i)) = LagrangianRing.rowTwenty S (M.map ρ) := by
  funext i
  rw [LagrangianRing.rowTwenty_eq_minor, LagrangianRing.rowTwenty_eq_minor]
  exact RingHom.map_det ρ (M.submatrix id (LagrangianRing.triple i))

theorem rowFourteen_map {R : Type u} [CommRing R]
    (κ : K →+* R) (ρ : R →+* K) (hρκ : ρ.comp κ = RingHom.id K)
    (M : Matrix (Fin 3) (Fin 6) R) :
    (fun i => ρ (LagrangianRing.rowFourteen R κ M i)) =
      LagrangianField.rowFourteen K (M.map ρ) := by
  rw [← LagrangianRing.rowFourteen_id_eq_field K (M.map ρ)]
  funext i
  change ρ (∑ j : Fin 20, κ (LagrangianField.projectionMatrix K i j) *
      LagrangianRing.rowTwenty R M j) =
    ∑ j : Fin 20, LagrangianField.projectionMatrix K i j *
      LagrangianRing.rowTwenty K (M.map ρ) j
  have hρκ_apply (a : K) : ρ (κ a) = a := RingHom.congr_fun hρκ a
  simp only [map_sum, map_mul, hρκ_apply, congrFun (rowTwenty_map ρ M)]

theorem chartCoordinates_eq_rowFourteen (p : Spec (.of K) ⟶ space K)
    (hp : p ≫ projection K = 𝟙 _) :
    LagrangianFieldCoordinates.values K
      (LagrangianPlucker.chartCoordinates K p (pointChart K p).index (pointChart K p).map) =
      LagrangianField.rowFourteen K (matrix K p) := by
  let ρ := (Scheme.ΓSpecIso (.of K)).hom.hom
  have hρκ : ρ.comp (LagrangianPlucker.coefficientMap K p) = RingHom.id K := by
    ext a
    change (Scheme.ΓSpecIso (.of K)).hom
      (((Scheme.ΓSpecIso (.of K)).inv ≫ (p ≫ projection K).appTop) a) = a
    rw [hp]
    simpa only [Scheme.Hom.id_appTop, Category.comp_id] using
      (Scheme.ΓSpecIso (.of K)).inv_hom_id_apply a
  have h := rowFourteen_map K (LagrangianPlucker.coefficientMap K p) ρ hρκ
    (Stacks.FreeSheafMatrix.toMatrix (Grassmannian.chartQuotientMap 3 6
      (pointChart K p).index (pointChart K p).map))
  funext j
  change (Scheme.ΓSpecIso (.of K)).hom
    (LagrangianPlucker.chartCoordinates K p (pointChart K p).index (pointChart K p).map j) = _
  simpa only [LagrangianPlucker.chartCoordinates, matrix, matrixOnField,
    Grassmannian.toMatrix_chartQuotientMap, ρ] using congrFun h j

end CoefficientComparison
end M9Native.LagrangianPointKernelCoordinates
