module

public import M9StacksIntegration.MukaiConormalChartImage
public import M9StacksIntegration.MukaiConormalChartCovariance
public import M9StacksIntegration.LagrangianRationalTranslatedPoint

/-! Actual inverse-dual covariance of the original conormal Euler image
at rational native LG points. The proof uses the genuine chart image
identification and the actual translated quotient frame. The base
identity is essential: arbitrary scheme maps Spec K → LG_K may induce
nonidentity endomorphisms of the coefficient field. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Module

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  SheafOfModules.unit PresheafOfModules.unit AlgebraicGeometry.SheafedSpace.sheaf

namespace M9Native.MukaiConormalNativeCovariance

open LagrangianGrassmannian LagrangianTranslatedCharts LagrangianSymplecticAction
open MukaiConormalFieldCoordinates MukaiConormalChartJets MukaiConormalChartCovariance
open LagrangianRationalTranslatedPoint LagrangianTranslatedDeterminantSections

variable (K : Type u) [Field K] [CharZero K] [IsAlgClosed K]

/-- The genuine native image identification specialized to the actual
translated quotient frame. No image equality is supplied as an input. -/
theorem translated_range (z : Spec (.of K) ⟶ chart K)
    (hz : z ≫ chartProjection K = 𝟙 _) (g : Matrix.symplecticGroup (Fin 3) K) :
    LinearMap.range (formsMap K (z ≫ translatedBigCell K g)) =
      LinearMap.ker (firstJetMap K z (sectionTuple K g)) := by
  have hf : translatedBigCell K g ≫ projection K = chartProjection K :=
    translatedBigCell_projection K g
  exact MukaiConormalChartImage.range_formsMap_eq_ker_firstJetMap K
      (translatedBigCell K g) hf z hz (translatedDeterminantIso K g)

/-- The original conormal Euler image transforms by the inverse dual
of the actual positive primitive action at every actual rational point. -/
theorem range_formsMap_action (p : Spec (.of K) ⟶ space K)
    (hp : p ≫ projection K = 𝟙 _) (g : Matrix.symplecticGroup (Fin 3) K) :
    LinearMap.range (formsMap K (p ≫ action K g)) =
      (LinearMap.range (formsMap K p)).map
        (MukaiPrimitiveQuartic.quotientMap K (LagrangianTransitivity.matrixSix K g⁻¹).mulVecLin) := by
  obtain ⟨h,z,hp',hz⟩ := exists_rational_chart K p hp
  have hpoint : p ≫ action K g = z ≫ translatedBigCell K (h*g) :=
    (congrArg (fun f => f ≫ action K g) hp'.symm).trans (factor_action K z h g)
  calc
    _ = LinearMap.range (formsMap K (z ≫ translatedBigCell K (h*g))) :=
      congrArg (fun f => LinearMap.range (formsMap K f)) hpoint
    _ = LinearMap.ker (firstJetMap K z (sectionTuple K (h*g))) :=
      translated_range K z hz (h*g)
    _ = (LinearMap.ker (firstJetMap K z (sectionTuple K h))).map
        (MukaiPrimitiveQuartic.quotientMap K (LagrangianTransitivity.matrixSix K g⁻¹).mulVecLin) :=
      firstJet_kernel_mul K z hz h g
    _ = _ := congrArg
      (fun S => S.map
        (MukaiPrimitiveQuartic.quotientMap K (LagrangianTransitivity.matrixSix K g⁻¹).mulVecLin))
      ((translated_range K z hz h).symm.trans
        (congrArg (fun f => LinearMap.range (formsMap K f)) hp'))

/-- For the canonical map of a closed point the actual rational base
identity is derived by the native closed-point construction. -/
theorem range_formsMap_closedPoint_action (x : space K)
    (hx : IsClosed ({x} : Set (space K))) (g : Matrix.symplecticGroup (Fin 3) K) :
    LinearMap.range (formsMap K (pointOfClosedPoint (projection K) x hx ≫ action K g)) =
      (LinearMap.range (formsMap K (pointOfClosedPoint (projection K) x hx))).map
        (MukaiPrimitiveQuartic.quotientMap K (LagrangianTransitivity.matrixSix K g⁻¹).mulVecLin) :=
  range_formsMap_action K _ (pointOfClosedPoint_comp _ _ _) g

end M9Native.MukaiConormalNativeCovariance
