module

public import M9StacksIntegration.GrassmannianExteriorIntersection
public import M9StacksIntegration.MukaiProjectiveCoordinateTransport

/-!
# Actual field-chart rows and actual exterior equations

The actual native quotient-chart matrix has identity pivot columns, hence
its actual three rows are independent. The native Pluecker coordinates
are exactly their actual exterior coordinates. The already proved native
projective-coordinate transport therefore identifies membership in the
genuine lifted linear section with vanishing of the actual exterior map.
No decomposable-point formula or coordinate identification is a premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open AlgebraicGeometry.ProjectiveSpaceOfModule

namespace M9Native.GrassmannianExteriorFieldCoordinates
open GrassmannianExteriorIntersection LagrangianPluckerLinear LagrangianPluckerClosed
open MukaiProjectiveEvaluationPoint MukaiProjectiveCoordinateTransport
universe u
variable (K : Type u) [Field K]

abbrev fieldChart (ι : Fin 3 ↪ Fin 6) : Scheme.{u} :=
  Spec (.of (MvPolynomial (Grassmannian.ChartIndex.{u} (k := 3) (n := 6) ι) (ULift.{u} ℤ)))

/-- Evaluation of the genuine full coordinate forms on the genuine row
trivector of an actual3-by6 matrix. -/
def pluckerFunctional (A : Matrix (Fin 3) (Fin 6) K) : Module.Dual K (Forms K) :=
  (Module.Dual.eval K (Exterior K) (LagrangianField.rowPlucker K A)).comp
    (coordinateLinearMap K)

theorem pluckerFunctional_basis (A : Matrix (Fin 3) (Fin 6) K)
    (i : Fin (Grassmannian.pluckerDim 3 6+1)) :
    pluckerFunctional K A (fullBasis K i) =
      (A.submatrix id ((Grassmannian.pluckerIndexEquiv 3 6).symm i)).det := by
  change coordinateLinearMap K (fullBasis K i) (LagrangianField.rowPlucker K A) = _
  rw [fullBasis_apply, coordinateLinearMap, Basis.constr_basis]
  exact LagrangianField.coordinate3_rowPlucker K A _

variable {H : Type u} [AddCommGroup H] [Module K H]

theorem pluckerFunctional_liftedDual (D : Exterior K →ₗ[K] H)
    (A : Matrix (Fin 3) (Fin 6) K) (ell : Module.Dual K (LinearMap.range D)) :
    pluckerFunctional K A (liftedDual K D ell) =
      ell (D.rangeRestrict (LagrangianField.rowPlucker K A)) := by
  change coordinateLinearMap K (dualLift K (D.rangeRestrict.dualMap ell))
      (LagrangianField.rowPlucker K A) = _
  rw [coordinateLinearMap_dualLift]
  rfl

/-- The actual original-K matrix of a native Grassmannian chart. -/
def matrixOnField (ι : Fin 3 ↪ Fin 6)
    (g : Spec (.of K) ⟶ fieldChart ι) :
    Matrix (Fin 3) (Fin 6) K :=
  (Grassmannian.chartMatrix (k := 3) (n := 6) ι (AffineSpace.toSpecMvPolyIntEquiv _ g)).map
    (Scheme.ΓSpecIso (.of K)).hom.hom

theorem matrixOnField_pivots (ι : Fin 3 ↪ Fin 6) (g : Spec (.of K) ⟶ fieldChart ι) :
    (matrixOnField K ι g).submatrix id ι = 1 := by
  have h : (Grassmannian.chartMatrix (k := 3) (n := 6) ι (AffineSpace.toSpecMvPolyIntEquiv _ g)).submatrix id ι = 1 := by
    ext i j
    simpa only [Matrix.submatrix_apply, id_eq, Matrix.one_apply] using
      Grassmannian.chartMatrix_apply_self (k := 3) (n := 6) ι (AffineSpace.toSpecMvPolyIntEquiv _ g) i j
  change ((Grassmannian.chartMatrix (k := 3) (n := 6) ι (AffineSpace.toSpecMvPolyIntEquiv _ g)).submatrix id ι).map
    (Scheme.ΓSpecIso (.of K)).hom.hom = 1
  rw [h]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem matrixOnField_rows_independent (ι : Fin 3 ↪ Fin 6) (g : Spec (.of K) ⟶ fieldChart ι) :
    LinearIndependent K (fun i => matrixOnField K ι g i) := by
  let P : (Fin 6 → K) →ₗ[K] (Fin 3 → K) := LinearMap.pi (fun j => LinearMap.proj (ι j))
  apply LinearIndependent.of_comp P
  change LinearIndependent K ((matrixOnField K ι g).submatrix id ι)
  apply Matrix.linearIndependent_rows_of_det_ne_zero
  rw [matrixOnField_pivots, Matrix.det_one]
  exact one_ne_zero

theorem pluckerFunctional_basis_chartValue (ι : Fin 3 ↪ Fin 6) (g : Spec (.of K) ⟶ fieldChart ι)
    (i : Fin (Grassmannian.pluckerDim 3 6+1)) :
    pluckerFunctional K (matrixOnField K ι g) (fullBasis K i) =
      (Scheme.ΓSpecIso (.of K)).hom (Grassmannian.pluckerSections (k := 3) (n := 6) ι g i) := by
  rw [pluckerFunctional_basis]
  change (((Grassmannian.chartMatrix (k := 3) (n := 6) ι (AffineSpace.toSpecMvPolyIntEquiv _ g)).submatrix id
      ((Grassmannian.pluckerIndexEquiv 3 6).symm i)).map
        (Scheme.ΓSpecIso (.of K)).hom.hom).det = _
  exact (RingHom.map_det (Scheme.ΓSpecIso (.of K)).hom.hom _).symm

/-- On EVERY actual native quotient chart, the original field Pluecker
map is the actual projective morphism of its actual minors. -/
theorem comp_nativeGrassPlucker (p : Spec (.of K) ⟶ grass K) (ι : Fin 3 ↪ Fin 6) (g : Spec (.of K) ⟶ fieldChart ι)
    (hpg : p ≫ pullback.snd _ _ = g ≫ Grassmannian.chart 3 6 ι) :
    p ≫ nativeGrassPlucker K =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver
        (Grassmannian.pluckerSections (k := 3) (n := 6) ι g) (Grassmannian.span_pluckerSections (k := 3) (n := 6) ι g)
        (p ≫ LagrangianGrassmannian.grassmannianProjection K) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, nativeGrassPlucker_projection,
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver_fst]
  · rw [Category.assoc, nativeGrassPlucker_toIntegral, ← Category.assoc, hpg,
      Category.assoc, Grassmannian.chart_comp_pluckerMap, Grassmannian.comp_chartPluckerMap,
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver_snd]

/-- Actual native projective coordinates of the actual field-chart
matrix, over the SAME original scalar identity. -/
theorem nativePoint_coordinates (p : Spec (.of K) ⟶ grass K)
    (hp : p ≫ LagrangianGrassmannian.grassmannianProjection K = 𝟙 _)
    (ι : Fin 3 ↪ Fin 6) (g : Spec (.of K) ⟶ fieldChart ι)
    (hpg : p ≫ pullback.snd _ _ = g ≫ Grassmannian.chart 3 6 ι)
    (x : Spec (.of K)) :
    ∃ hφ : pluckerFunctional K (matrixOnField K ι g) ≠ 0,
      (fullProjectiveIso K).hom (nativeGrassPlucker K (p x)) =
        linearFunctionalPoint K (Forms K) (pluckerFunctional K (matrixOnField K ι g)) hφ := by
  let φ := pluckerFunctional K (matrixOnField K ι g)
  let i := Grassmannian.pluckerIndexEquiv 3 6 ι
  have hi : φ (fullBasis K i) = 1 := by
    rw [pluckerFunctional_basis_chartValue, Grassmannian.pluckerSections_self]
    exact _root_.map_one (Scheme.ΓSpecIso (.of K)).hom.hom
  have hφ : φ ≠ 0 := by
    intro hz
    rw [hz, LinearMap.zero_apply] at hi
    exact zero_ne_one hi
  have hs (j : Fin (Grassmannian.pluckerDim 3 6+1)) :
      scalarSections K (φ (fullBasis K j)) = Grassmannian.pluckerSections (k := 3) (n := 6) ι g j := by
    rw [pluckerFunctional_basis_chartValue]
    exact (Scheme.ΓSpecIso (.of K)).hom_inv_id_apply _
  have hq : (p ≫ nativeGrassPlucker K) ≫ pullback.fst _ _ = 𝟙 _ := by
    rw [Category.assoc, nativeGrassPlucker_projection, hp]
  have hint : (p ≫ nativeGrassPlucker K) ≫ projectiveSpaceOver.toIntegralAtUniverse
      (Grassmannian.pluckerDim 3 6) (Spec (.of K)) =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse
        (fun j => scalarSections K (φ (fullBasis K j)))
        (span_scalarSections K _ i hi) := by
    rw [comp_nativeGrassPlucker K p ι g hpg,
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver_snd]
    exact Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse_congr
      (funext fun j => (hs j).symm) _ _
  refine ⟨hφ, ?_⟩
  exact coordinateTransport_base K (Forms K) (fullBasis K) (p ≫ nativeGrassPlucker K)
    φ hφ i hi hq hint x

/-- Membership of the actual native Pluecker point in the actual
lifted linear section is exactly vanishing of the ORIGINAL exterior map. -/
theorem nativePoint_mem_iff (D : Exterior K →ₗ[K] H) (p : Spec (.of K) ⟶ grass K)
    (hp : p ≫ LagrangianGrassmannian.grassmannianProjection K = 𝟙 _)
    (ι : Fin 3 ↪ Fin 6) (g : Spec (.of K) ⟶ fieldChart ι)
    (hpg : p ≫ pullback.snd _ _ = g ≫ Grassmannian.chart 3 6 ι) (x : Spec (.of K)) :
    nativeGrassPlucker K (p x) ∈ linearSection K D ↔
      D (LagrangianField.rowPlucker K (matrixOnField K ι g)) = 0 := by
  obtain ⟨hφ, hc⟩ := nativePoint_coordinates K p hp ι g hpg x
  change (fullProjectiveIso K).hom (nativeGrassPlucker K (p x)) ∈
    linearSubspace K (Forms K) (constraints K D) ↔ _
  rw [hc, mem_linearSubspace_iff, pointSubmodule_linearFunctionalPoint]
  constructor
  · intro h
    have hz : D.rangeRestrict (LagrangianField.rowPlucker K (matrixOnField K ι g)) = 0 := by
      apply Module.eval_apply_injective K
      ext ell
      change ell (D.rangeRestrict (LagrangianField.rowPlucker K (matrixOnField K ι g))) = ell 0
      rw [map_zero]
      have he := h ⟨ell, rfl⟩
      change pluckerFunctional K (matrixOnField K ι g) (liftedDual K D ell) = 0 at he
      rwa [pluckerFunctional_liftedDual] at he
    exact congrArg Subtype.val hz
  · intro h
    rintro ell ⟨ξ, rfl⟩
    change pluckerFunctional K (matrixOnField K ι g) (liftedDual K D ξ) = 0
    rw [pluckerFunctional_liftedDual]
    have hz : D.rangeRestrict (LagrangianField.rowPlucker K (matrixOnField K ι g)) = 0 :=
      Subtype.ext h
    rw [hz, map_zero]

end M9Native.GrassmannianExteriorFieldCoordinates
