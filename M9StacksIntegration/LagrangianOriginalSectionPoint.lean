module

public import M9StacksIntegration.LagrangianPointKernelCoordinates
public import M9StacksIntegration.LagrangianTripleNaturality
public import M9StacksIntegration.LagrangianHyperplaneEvaluation
public import M9StacksIntegration.CanonicalZeroSchemeEmpty

/-! The actual original quotient section and its pointwise matrix kernel.
The pullback comparisons, original scalar action and quotient triangles
are proved. A common vector in the constructed kernel planes therefore
annihilates the SAME original section and factors through its FULL zero
scheme; no support-only replacement is made. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite Matrix
open scoped BigOperators
universe u

namespace M9Native.LagrangianOriginalSectionPoint
open LagrangianMatrixChart LagrangianGrassmannian LagrangianUniversalSections
open LagrangianPointKernelCoordinates LagrangianPluckerTrivialization
open GrassmannianExteriorFieldCoordinates
open AlgebraicGeometry.Grassmannian SectionZeroIdealFactorization

variable (K : Type u) [Field K]

theorem freeCoordinates_map {X : Scheme.{u}} {n m : ℕ}
    (a : freeOn X n ⟶ freeOn X m) (s : Γ(freeOn X n,⊤)) :
    freeSectionCoordinates X m (a.app ⊤ s) =
      (Stacks.FreeSheafMatrix.toMatrix a).mulVec (freeSectionCoordinates X n s) := by
  have hs : a.app ⊤ s = ∑ j : Fin n,
      freeSectionCoordinates X n s j • a.app ⊤ (freeBasisSection X n j) := by
    conv_lhs => rw [LagrangianFreeMatrixPullback.eq_sum_coordinates_basis X n s]
    simp only [map_sum, Scheme.Modules.Hom.app_smul]
  have hb (j : Fin n) :
      freeSectionCoordinates X m (a.app ⊤ (freeBasisSection X n j)) =
        fun i => Stacks.FreeSheafMatrix.toMatrix a i j :=
    funext (fun i => freeCoordinates_map_basis a i j)
  rw [hs, map_sum]
  simp_rw [map_smul, hb]
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem constantVector_pullback {X Y : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (g : Y ⟶ X) (v : Fin 6 → K) :
    (pullbackFreeIso g 6).hom.app ⊤
      (pullbackGlobalSections g (freeOn X 6) (constantVector K f v)) =
        constantVector K (g ≫ f) v := by
  simp only [constantVector, map_sum, SectionsEqualizer.pullbackGlobalSections_smul,
    Scheme.Modules.Hom.app_smul, PrimitiveFreeMatrixPullback.freeBasisSection_pullback]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun a => a • freeBasisSection Y 6 i)
    (RingHom.congr_fun (LagrangianTripleNaturality.baseRingMap_comp K f g) (v i)).symm

theorem inverse_constantVector_pullback {X Y : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (g : Y ⟶ X) (v : Fin 6 → K) :
    (pullbackFreeIso g 6).inv.app ⊤ (constantVector K (g ≫ f) v) =
      pullbackGlobalSections g (freeOn X 6) (constantVector K f v) := by
  have h := congrArg ((pullbackFreeIso g 6).inv.app ⊤) (constantVector_pullback K f g v)
  change ((pullbackFreeIso g 6).hom ≫ (pullbackFreeIso g 6).inv).app ⊤
    (pullbackGlobalSections g (freeOn X 6) (constantVector K f v)) = _ at h
  rw [Iso.hom_inv_id] at h
  exact h.symm

def quotientPullbackIso {X Y : Scheme.{u}} (l : X ⟶ space K) (g : Y ⟶ X) :
    (Scheme.Modules.pullback g).obj (bundle K l) ≅ bundle K (g ≫ l) :=
  Classical.choose (pullbackPresentation_comp_isomorphic l g (LagrangianPluckerQuotient.quotientOnLG K))

theorem quotientPullbackIso_triangle {X Y : Scheme.{u}} (l : X ⟶ space K) (g : Y ⟶ X) :
    (pullbackFreeIso g 6).inv ≫ (Scheme.Modules.pullback g).map (quotientMap K l) ≫
      (quotientPullbackIso K l g).hom = quotientMap K (g ≫ l) :=
  Classical.choose_spec (pullbackPresentation_comp_isomorphic l g (LagrangianPluckerQuotient.quotientOnLG K))

theorem originalSection_pullback {X Y : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (l : X ⟶ space K) (g : Y ⟶ X) (v : Fin 6 → K) :
    (quotientPullbackIso K l g).hom.app ⊤
      (pullbackGlobalSections g (bundle K l)
        (LagrangianHyperplaneEvaluation.originalSection K f l v)) =
      (quotientMap K (g ≫ l)).app ⊤ (constantVector K (g ≫ f) v) := by
  have h := congrArg (fun a : freeOn Y 6 ⟶ bundle K (g ≫ l) =>
    a.app ⊤ (constantVector K (g ≫ f) v)) (quotientPullbackIso_triangle K l g)
  change (quotientPullbackIso K l g).hom.app ⊤
    (((Scheme.Modules.pullback g).map (quotientMap K l)).app ⊤
      ((pullbackFreeIso g 6).inv.app ⊤ (constantVector K (g ≫ f) v))) = _ at h
  rw [inverse_constantVector_pullback,
    pullback_map_app_pullbackGlobalSections] at h
  exact h

theorem originalSection_pullback_zero_iff {X Y : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (l : X ⟶ space K) (g : Y ⟶ X) (v : Fin 6 → K) :
    pullbackGlobalSections g (bundle K l)
      (LagrangianHyperplaneEvaluation.originalSection K f l v) = 0 ↔
      (quotientMap K (g ≫ l)).app ⊤ (constantVector K (g ≫ f) v) = 0 := by
  rw [← originalSection_pullback K f l g v]
  exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    ((quotientPullbackIso K l g).hom.app ⊤)).injective).symm

theorem constantVector_spec_coordinates (v : Fin 6 → K) :
    freeSectionCoordinates (Spec (.of K)) 6 (constantVector K (𝟙 _) v) =
      fun i => (Scheme.ΓSpecIso (.of K)).inv (v i) := by
  have hκ : ExteriorEvaluation.baseRingMap K (𝟙 (Spec (.of K))) =
      (Scheme.ΓSpecIso (.of K)).inv.hom := by
    unfold ExteriorEvaluation.baseRingMap
    rw [appLE_top_top_eq_appTop, Scheme.Hom.id_appTop, Category.comp_id]
  have hb (j : Fin 6) :
      freeSectionCoordinates (Spec (.of K)) 6 (freeBasisSection (Spec (.of K)) 6 j) =
        Pi.single j 1 := by
    funext i
    simpa only [Pi.single_apply] using LagrangianFreeMatrixPullback.freeCoordinates_basis
      (Spec (.of K)) 6 i j
  change freeSectionCoordinates (Spec (.of K)) 6
    (∑ j : Fin 6, ExteriorEvaluation.baseRingMap K (𝟙 _) (v j) •
      freeBasisSection (Spec (.of K)) 6 j) = _
  rw [map_sum]
  simp_rw [map_smul, hb, hκ]
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ = (Scheme.ΓSpecIso (.of K)).inv.hom (v i) := by simp [Pi.single_apply, eq_comm]
    _ = (Scheme.ΓSpecIso (.of K)).inv (v i) := rfl

theorem matrix_spec_scalar_zero_iff {n m : ℕ}
    (M : Matrix (Fin m) (Fin n) Γ(Spec (.of K),⊤)) (v : Fin n → K) :
    M.mulVec (fun j => (Scheme.ΓSpecIso (.of K)).inv (v j)) = 0 ↔
      (M.map (Scheme.ΓSpecIso (.of K)).hom.hom).mulVec v = 0 := by
  let ρ := (Scheme.ΓSpecIso (.of K)).hom.hom
  let κ := (Scheme.ΓSpecIso (.of K)).inv.hom
  change M.mulVec (κ ∘ v) = 0 ↔ (M.map ρ).mulVec v = 0
  have hρκ (a : K) : ρ (κ a) = a := (Scheme.ΓSpecIso (.of K)).inv_hom_id_apply a
  constructor
  · intro h
    funext i
    have hi := congrArg ρ (congrFun h i)
    rw [RingHom.map_mulVec] at hi
    simpa only [Function.comp_def, hρκ, Pi.zero_apply, map_zero] using hi
  · intro h
    funext i
    apply (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.injective
    change ρ (M.mulVec (κ ∘ v) i) = ρ 0
    rw [RingHom.map_mulVec, map_zero]
    simpa only [Function.comp_def, hρκ, Pi.zero_apply] using congrFun h i

theorem point_quotient_zero_iff_matrix (p : Spec (.of K) ⟶ space K) (v : Fin 6 → K) :
    (quotientMap K p).app ⊤ (constantVector K (𝟙 _) v) = 0 ↔
      (matrix K p).mulVec v = 0 := by
  let d := pointChart K p
  let e := chartQuotientIso K p d.index d.map d.triangle
  let q : freeOn (Spec (.of K)) 6 ⟶ freeOn (Spec (.of K)) 3 :=
    Grassmannian.chartQuotientMap 3 6 d.index d.map
  have ht : quotientMap K p ≫ e.hom = q := chartQuotientIso_triangle K p d.index d.map d.triangle
  have he : (quotientMap K p).app ⊤ (constantVector K (𝟙 _) v) = 0 ↔
      q.app ⊤ (constantVector K (𝟙 _) v) = 0 := by
    rw [← ht]
    exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).injective).symm
  rw [he]
  have hc := freeCoordinates_map q (constantVector K (𝟙 _) v)
  rw [constantVector_spec_coordinates] at hc
  have hzero : q.app ⊤ (constantVector K (𝟙 _) v) = 0 ↔
      (Stacks.FreeSheafMatrix.toMatrix q).mulVec
        (fun j => (Scheme.ΓSpecIso (.of K)).inv (v j)) = 0 := by
    rw [← hc]
    exact (map_eq_zero_iff _ (freeSectionCoordinates (Spec (.of K)) 3).injective).symm
  rw [hzero, matrix_spec_scalar_zero_iff]
  simp only [matrix, matrixOnField, q, d, Grassmannian.toMatrix_chartQuotientMap]

theorem originalSection_point_zero_iff_matrix {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (l : X ⟶ space K)
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) (v : Fin 6 → K) :
    pullbackGlobalSections p (bundle K l)
      (LagrangianHyperplaneEvaluation.originalSection K f l v) = 0 ↔
      (matrix K (p ≫ l)).mulVec v = 0 := by
  rw [originalSection_pullback_zero_iff, hp]
  exact point_quotient_zero_iff_matrix K (p ≫ l) v

theorem originalSection_point_zero_of_kernel_span {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (l : X ⟶ space K)
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) (v : Fin 6 → K)
    (hv : v ∈ Submodule.span K (Set.range (kernelRows K (p ≫ l)))) :
    pullbackGlobalSections p (bundle K l)
      (LagrangianHyperplaneEvaluation.originalSection K f l v) = 0 :=
  (originalSection_point_zero_iff_matrix K f l p hp v).mpr
    (kernelRows_span_le_kernel K (p ≫ l) hv)

/-- Every original field point killed by the actual original section
factors through its SAME FULL native section-zero scheme. -/
theorem factors_full_zero_of_kernel_span {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (l : X ⟶ space K)
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) (v : Fin 6 → K)
    (hv : v ∈ Submodule.span K (Set.range (kernelRows K (p ≫ l)))) :
    ∃ t : Spec (.of K) ⟶ (LagrangianHyperplaneEvaluation.zeroIdeal K f l v).subscheme,
      t ≫ (LagrangianHyperplaneEvaluation.zeroIdeal K f l v).subschemeι = p := by
  let := bundle_rank K l
  have hzero := originalSection_point_zero_of_kernel_span K f l p hp v hv
  exact (pullbackGlobalSections_eq_zero_iff_factorsThrough (bundle K l) 3
    (LagrangianHyperplaneEvaluation.originalSection K f l v) p).mp hzero

end M9Native.LagrangianOriginalSectionPoint
