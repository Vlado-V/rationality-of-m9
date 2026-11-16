module

public import M9StacksIntegration.Sp6GaussChartDomain
public import M9StacksIntegration.Sp6GaussTranslatedCharts
public import M9StacksIntegration.Sp6IntegerAlgebraCoherence
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! Finite type of the actual Gauss parameter algebra and its base projection. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.Sp6GaussChartFiniteType

open Sp6GaussChartDomain
open Sp6AffineBaseChange (IntegerRing)

variable (K : Type u) [Field K]

local instance targetIntegerAlgebra : Algebra IntegerRing.{u} K :=
  Sp6AffineBaseChange.integerAlgebra K

instance polynomial_finiteType : Algebra.FiniteType K (PolynomialCoordinateRing K) :=
  (inferInstance : Algebra.FiniteType K (MvPolynomial (Fin 3 × Fin 3) K)).equiv
    (polynomialBaseChangeEquiv K).symm

instance linear_finiteType : Algebra.FiniteType K (LinearCoordinateRing K) := by
  let e : LinearCoordinateRing K ≃ₐ[K] Localization.Away (tensorDeterminant K) :=
    IsLocalization.Away.tensorProductEquivTMulRight IntegerRing.{u} K
      (generalLinearDeterminant.{u} 3) (generalLinearCoordinateRing.{u} 3)
  exact (inferInstance : Algebra.FiniteType K
    (Localization.Away (tensorDeterminant K))).equiv e.symm

instance chart_finiteType : Algebra.FiniteType K (ChartCoordinateRing K) :=
  (inferInstance : Algebra.FiniteType K
    (MvPolynomial Sp6GaussCellCoordinates.ExtraIndex (LinearCoordinateRing K))).equiv
      (chartBaseChangeEquiv K).symm

instance projection_locallyOfFiniteType :
    LocallyOfFiniteType (Sp6GaussBaseChart.projection K) := by
  have h : Over.mk (Sp6GaussBaseChart.projection K) =
      Over.mk (Sp6AffineBaseChange.specAlgebraMap K (ChartCoordinateRing K)) :=
    Sp6IntegerAlgebraCoherence.tensorOver_eq K Sp6GaussCellCoordinates.CoordinateRing
      (Sp6AffineBaseChange.integerAlgebra K) (Sp6AffineBaseChange.integerAlgebra K)
      (Sp6AffineBaseChange.integerAlgebra Sp6GaussCellCoordinates.CoordinateRing)
      (inferInstance : Algebra IntegerRing Sp6GaussCellCoordinates.CoordinateRing)
  have hd : LocallyOfFiniteType
      (Sp6AffineBaseChange.specAlgebraMap K (ChartCoordinateRing K)) := by
    change LocallyOfFiniteType (Spec.map
      (CommRingCat.ofHom (algebraMap K (ChartCoordinateRing K))))
    apply HasRingHomProperty.Spec_iff.mpr
    exact (RingHom.finiteType_algebraMap).mpr (chart_finiteType K)
  exact Eq.mpr (congrArg (fun V : Over (Spec (.of K)) => LocallyOfFiniteType V.hom) h) hd

/-- Finite type descends through the actual eight open charts. -/
instance group_projection_locallyOfFiniteType :
    LocallyOfFiniteType (Sp6GroupScheme.obj (Spec (.of K))).hom := by
  refine IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
    (Sp6GaussTranslatedCharts.admissibleCover K) fun s => ?_
  change LocallyOfFiniteType (Sp6GaussTranslatedCharts.chart K s ≫
    (Sp6GroupScheme.obj (Spec (.of K))).hom)
  rw [Sp6GaussTranslatedCharts.chart_projection]
  infer_instance

instance affine_projection_locallyOfFiniteType :
    LocallyOfFiniteType (Sp6AffineBaseChange.projection K) := by
  rw [← Sp6AffineBaseChange.affineIso_hom_projection]
  infer_instance

/-- This is finite type of the original affine algebra, not a
replacement presentation or an added geometric assumption. -/
instance coordinate_finiteType :
    Algebra.FiniteType K (Sp6AffineBaseChange.CoordinateRing K) := by
  have h : (algebraMap K (Sp6AffineBaseChange.CoordinateRing K)).FiniteType :=
    HasRingHomProperty.Spec_iff.mp (affine_projection_locallyOfFiniteType K)
  exact RingHom.finiteType_algebraMap.mp h

end M9Native.Sp6GaussChartFiniteType
