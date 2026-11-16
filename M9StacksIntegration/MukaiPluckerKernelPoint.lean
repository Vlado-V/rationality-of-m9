module

public import M9StacksIntegration.MukaiGrassmannianPlucker
public import M9StacksIntegration.MukaiProjectiveKernelCoordinates
public import M9StacksIntegration.MukaiProjectiveCoordinateTransport
public import M9StacksIntegration.MukaiPluckerMinorEvaluation

/-! # The original native Plücker point satisfies precisely the original linear equations -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open Module AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpaceOfModule
open M9Native.MukaiGrassmannianPlucker M9Native.MukaiProjectiveKernelCoordinates
open M9Native.MukaiProjectiveEvaluationPoint M9Native.MukaiProjectiveCoordinateTransport

universe u

namespace M9Native.MukaiPluckerKernelPoint

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse

variable (K : Type u) [Field K]

theorem minorFunctional_basis (M : Matrix (Fin 2) (Fin 5) K)
    (t : Fin (Grassmannian.pluckerDim 3 5 + 1)) :
    minorFunctional K M (ambientBasis K t) =
      MukaiOrderedMinors.orderedMinorCoordinates (M 0) (M 1)
        ((Grassmannian.pluckerIndexEquiv 3 5).symm t) := by
  exact eval_reindexed_dualBasis K (Grassmannian.pluckerIndexEquiv 3 5)
    (MukaiOrderedMinors.orderedMinorCoordinates (M 0) (M 1)) t

theorem minorFunctional_pivot (ι : MukaiOrderedMinors.OrderedPair)
    (M : Matrix (Fin 2) (Fin 5) K) (hM : M.submatrix id ι = 1) :
    minorFunctional K M (ambientBasis K (Grassmannian.pluckerIndexEquiv 3 5 ι)) = 1 := by
  rw [minorFunctional_basis,Equiv.symm_apply_apply,orderedMinors_pivot K ι M hM]

/-- The actual native pulled-back chart sections are the literal twenty minors in the dual basis. -/
theorem matrixPoint_pluckerSections (ι : MukaiOrderedMinors.OrderedPair)
    (M : Matrix (Fin 2) (Fin 5) K) (hM : M.submatrix id ι = 1) :
    Grassmannian.pluckerSections (k := 3) (n := 5) ι (GrassmannianCharts.matrixPoint K 3 5 ι M) =
      fun t => scalarSections K (minorFunctional K M (ambientBasis K t)) := by
  funext t
  rw [Grassmannian.pluckerSections,GrassmannianCharts.matrixPoint_chartMatrix K 3 5 ι M hM,
    Grassmannian.plucker_map,minorFunctional_basis]
  congr 1
  exact (MukaiOrderedMinors.orderedMinorCoordinates_eq_det M _).symm

/-- The two genuine projections of the original native Plücker morphism, specialized to a chart. -/
theorem matrixPoint_pluckerOver_toIntegral (ι : MukaiOrderedMinors.OrderedPair)
    (M : Matrix (Fin 2) (Fin 5) K) (hM : M.submatrix id ι = 1) :
    (matrixPoint K ι M ≫ pluckerOver K) ≫
        projectiveSpaceOver.toIntegralAtUniverse (Grassmannian.pluckerDim 3 5) (Spec (.of K)) =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse
        (fun t => scalarSections K (minorFunctional K M (ambientBasis K t)))
        (span_scalarSections K _ (Grassmannian.pluckerIndexEquiv 3 5 ι)
          (minorFunctional_pivot K ι M hM)) := by
  calc
    (matrixPoint K ι M ≫ pluckerOver K) ≫ _ =
        matrixPoint K ι M ≫ GrassmannianCharts.toIntegral K 3 5 ≫ Grassmannian.pluckerMap 3 5 := by
      simp only [pluckerOver,projectiveSpaceOver.toIntegralAtUniverse,Category.assoc,
        pullback.map,pullback.lift_snd,GrassmannianCharts.toIntegral]
    _ = GrassmannianCharts.matrixPoint K 3 5 ι M ≫ Grassmannian.chart 3 5 ι ≫
        Grassmannian.pluckerMap 3 5 := by rw [← Category.assoc,matrixPoint_toIntegral,Category.assoc]
    _ = GrassmannianCharts.matrixPoint K 3 5 ι M ≫ Grassmannian.chartPluckerMap (k := 3) (n := 5) ι := by
      rw [Grassmannian.chart_comp_pluckerMap]
    _ = _ := by
      rw [Grassmannian.comp_chartPluckerMap]
      exact Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse_congr
        (matrixPoint_pluckerSections K ι M hM) _ _

/-- This is the original native Grassmannian Plücker point, not an assumed coordinate point. -/
theorem matrixPoint_plucker_eq_coordinatePoint (ι : MukaiOrderedMinors.OrderedPair)
    (M : Matrix (Fin 2) (Fin 5) K) (hM : M.submatrix id ι = 1) :
    plucker K (matrixPoint K ι M (IsLocalRing.closedPoint K)) =
      coordinatePoint K (MukaiOrderedMinors.orderedMinorCoordinates (M 0) (M 1))
        (orderedMinors_ne_zero K ι M hM) := by
  have hbase : (matrixPoint K ι M ≫ pluckerOver K) ≫
      pullback.fst (terminal.from (Spec (.of K)))
        (terminal.from (projectiveSpaceAtUniverse.{u} (Grassmannian.pluckerDim 3 5))) = 𝟙 _ := by
    simp only [pluckerOver,Category.assoc,pullback.map,pullback.lift_fst,Category.comp_id]
    exact matrixPoint_projection K ι M
  have he := coordinateTransport_base K (AmbientForms K) (ambientBasis K)
    (matrixPoint K ι M ≫ pluckerOver K) (minorFunctional K M)
    (evaluation_ne_zero K _ (orderedMinors_ne_zero K ι M hM))
    (Grassmannian.pluckerIndexEquiv 3 5 ι) (minorFunctional_pivot K ι M hM)
    hbase (matrixPoint_pluckerOver_toIntegral K ι M hM) (IsLocalRing.closedPoint K)
  simpa only [plucker,Scheme.Hom.comp_apply,coordinatePoint,minorFunctional] using he

/-- Actual native projective membership is exactly vanishing under the original map on all twenty minors. -/
theorem matrixPoint_mem_kernelLinearSubspace_iff {Z : Type u} [AddCommGroup Z] [Module K Z]
    (L : Coordinates K →ₗ[K] Z) (ι : MukaiOrderedMinors.OrderedPair)
    (M : Matrix (Fin 2) (Fin 5) K) (hM : M.submatrix id ι = 1) :
    plucker K (matrixPoint K ι M (IsLocalRing.closedPoint K)) ∈ kernelLinearSubspace K L ↔
      L (MukaiOrderedMinors.orderedMinorCoordinates (M 0) (M 1)) = 0 := by
  rw [matrixPoint_plucker_eq_coordinatePoint K ι M hM,coordinatePoint_mem_iff]

end M9Native.MukaiPluckerKernelPoint
