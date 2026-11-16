module

public import M9StacksIntegration.MukaiConormalRowFirstJet
public import M9StacksIntegration.MukaiLocalCotangentPullback
public import M9StacksIntegration.MukaiFramedLocalDerivative

/-!
# The original point conormal kernel annihilates the full translated LG first jet

The original row-coordinate law, actual positive conormal differential,
and native local-to-framed derivative comparison are assembled without
an additional frame or jet comparison input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  SheafOfModules.unit PresheafOfModules.unit AlgebraicGeometry.SheafedSpace.sheaf

universe u
namespace M9Native.MukaiConormalRowFirstJet

open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianMatrixChart
open MukaiConormalChartJets LagrangianTranslatedCharts LagrangianTranslatedDeterminantSections
open MukaiConormalChartCovariance MukaiConormalOriginCoordinates LagrangianFieldJetCoefficients

private theorem pulledSection_zero_transport
    (K : Type u) [Field K] {Y : Scheme.{u}} (N : Y.Modules) (U : Y.Opens)
    (t t' : Spec (.of K) ⟶ Y) (h : t = t')
    (ht : t.base (SpecFieldStalkSections.point K) ∈ U)
    (ht' : t'.base (SpecFieldStalkSections.point K) ∈ U)
    (s : Γ(N,U))
    (hs : SpecFieldPullbackSections.pulledSection K t' N U ht' s = 0) :
    SpecFieldPullbackSections.pulledSection K t N U ht s = 0 := by
  subst t'
  exact hs

/-- A zero of the actual original point-conormal map annihilates the
FULL first jet of the literal original row in the actual translated LG
chart. Both source coordinates and differential comparison are derived. -/
theorem pointSequenceMap_zero_implies_firstJet_zero
    (K : Type u) [Field K] [CharZero K] {X : Scheme.{u}}
    (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
    (i : X ⟶ space K) [IsClosedImmersion i]
    (q : X ⟶ LagrangianFibreFactorization.fibre K
      (LagrangianMatrixPointRows.matrixPoint K M hM))
    (hq : q ≫ LagrangianFibreFactorization.fibreToLG K
      (LagrangianMatrixPointRows.matrixPoint K M hM) = i)
    (p : Spec (.of K) ⟶ X) (hp : p ≫ (i ≫ projection K) = 𝟙 _)
    (g : Matrix.symplecticGroup (Fin 3) K) (z : Spec (.of K) ⟶ chart K)
    (hz : z ≫ translatedBigCell K g = p ≫ i) (a : Fin 5 → K)
    (ha : pointSequenceMap K M hM i q hq p g z hz a = 0) :
    firstJetMap K z (sectionTuple K g)
      ((formsCoordinates K).symm (Matrix.vecMul a M)) = 0 := by
  let h := translatedBigCell K g
  let U := translatedOpen K g
  have hU : (⊤ : (chart K).Opens) ≤ h ⁻¹ᵁ U := by
    intro x _
    change h.base x ∈ Set.range h.base
    exact ⟨x,rfl⟩
  have hh : h ≫ projection K = chartProjection K := translatedBigCell_projection K g
  have hzbase := chart_point_overBase K i p g z hz hp
  have hvalue := original_row_value_zero K i p g z hz M hM q hq hp a
  have hv : pointValue K z (framedSection K g (Matrix.vecMul a M)) = 0 :=
    (framedSection_value K g z hzbase (Matrix.vecMul a M)).trans hvalue
  obtain ⟨m,hm⟩ := translatedLocalFunctional_pairing_one K g
  have hd := translated_local_derivative_zero K i p g z hz M hM q hq hp a ha
  have hd' : SpecFieldPullbackSections.pulledSection K (z ≫ h)
      (Scheme.Hom.relativeDifferentials (projection K)) U
      (MukaiLocalCotangentPullback.point_mem K h z U hU)
      ((Scheme.Hom.universalRelativeDerivation (projection K)).d
        (evalAt (determinantLine K) (translatedLocalFunctional K g)
          ((determinantLine K).presheaf.map (homOfLE le_top).op
            (LagrangianHyperplaneCoordinates.determinantSection K (Matrix.vecMul a M))))) = 0 := by
    exact pulledSection_zero_transport K
      (Scheme.Hom.relativeDifferentials (projection K)) U (z ≫ h) (p ≫ i) hz
      (MukaiLocalCotangentPullback.point_mem K h z U hU)
      (point_mem_translatedOpen K i p g z hz) _ hd
  have hderivative :=
    MukaiFramedLocalDerivative.pointDerivative_eq_zero_of_local_dual_evaluation
      K (projection K) h (chartProjection K) hh z (determinantLine K) U hU
      (translatedDeterminantIso K g) (translatedLocalFunctional K g) m hm
      (LagrangianHyperplaneCoordinates.determinantSection K (Matrix.vecMul a M)) hv hd'
  apply Prod.ext
  · exact hvalue
  · exact (framedSection_derivative K g z hzbase (Matrix.vecMul a M)).symm.trans hderivative

end M9Native.MukaiConormalRowFirstJet
