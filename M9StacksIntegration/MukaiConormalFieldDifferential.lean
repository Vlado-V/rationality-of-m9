module

public import M9StacksIntegration.MukaiConormalDifferentialTransport
public import M9StacksIntegration.MukaiConormalFieldCoordinates
public import M9StacksIntegration.SpecFieldEpimorphism
public import M9StacksIntegration.ProjectiveEulerFieldPoint

/-! The actual field-point cotangent differential of the original
primitive embedding is surjective; its target has genuine dimension six. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

namespace M9Native.MukaiConormalFieldDifferential

open LagrangianGrassmannian MukaiConormalCotangentTransport MukaiConormalDifferentialTransport

variable (K : Type u) [Field K] [CharZero K] [IsAlgClosed K]

abbrev CotangentSource (p : Spec (.of K) ⟶ space K) :=
  moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (p ≫ LagrangianPlucker.integralPrimitivePlucker K)).obj
    (Scheme.Hom.relativeDifferentials (integralProjection 13)))

abbrev CotangentTarget (p : Spec (.of K) ⟶ space K) :=
  moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj
    (Scheme.Hom.relativeDifferentials (projection K)))

def differentialSheaf (p : Spec (.of K) ⟶ space K) :
    (Scheme.Modules.pullback (p ≫ LagrangianPlucker.integralPrimitivePlucker K)).obj
        (Scheme.Hom.relativeDifferentials (integralProjection 13)) ⟶
      (Scheme.Modules.pullback p).obj (Scheme.Hom.relativeDifferentials (projection K)) :=
  (Scheme.Modules.pullbackComp p (LagrangianPlucker.integralPrimitivePlucker K)).inv.app
    (Scheme.Hom.relativeDifferentials (integralProjection 13)) ≫
      (Scheme.Modules.pullback p).map (integralDifferential K)

def differential (p : Spec (.of K) ⟶ space K) :
    CotangentSource K p →ₗ[K] CotangentTarget K p :=
  (moduleSpecΓFunctor.map (differentialSheaf K p)).hom

theorem integralDifferential_epi : Epi (integralDifferential K) := by
  have h : integralDifferential K = (MukaiConormalRank.ambientIntegralIso K).inv ≫
      MukaiConormalSequence.differential K := by
    calc
      _ = (MukaiConormalRank.ambientIntegralIso K).inv ≫
          ((MukaiConormalRank.ambientIntegralIso K).hom ≫ integralDifferential K) := by simp
      _ = _ := congrArg (fun t => (MukaiConormalRank.ambientIntegralIso K).inv ≫ t)
        (ambientIntegralIso_comp_integralDifferential K)
  rw [h]
  infer_instance

theorem differentialSheaf_epi (p : Spec (.of K) ⟶ space K) : Epi (differentialSheaf K p) := by
  let F := Scheme.Modules.pullback p
  let : Epi (integralDifferential K) := integralDifferential_epi K
  let : F.PreservesEpimorphisms := CategoryTheory.Functor.preservesEpimorphisms_of_adjunction
    (Scheme.Modules.pullbackPushforwardAdjunction p)
  have hMap : Epi (F.map (integralDifferential K)) := F.map_epi _
  let e := ((Scheme.Modules.pullbackComp p (LagrangianPlucker.integralPrimitivePlucker K)).app
    (Scheme.Hom.relativeDifferentials (integralProjection 13))).symm
  let : Epi e.hom := IsIso.epi_of_iso e.hom
  change Epi (e.hom ≫ F.map (integralDifferential K))
  exact (epi_comp_iff_of_epi e.hom _).mpr hMap

theorem differential_surjective (p : Spec (.of K) ⟶ space K) :
    Function.Surjective (differential K p) := by
  let : Epi (differentialSheaf K p) := differentialSheaf_epi K p
  exact SpecFieldEpimorphism.sections_surjective K (differentialSheaf K p)

omit [CharZero K] [IsAlgClosed K] in
theorem target_finite_and_finrank (p : Spec (.of K) ⟶ space K) :
    Module.Finite K (CotangentTarget K p) ∧ finrank K (CotangentTarget K p) = 6 := by
  let := LagrangianDegree.lagrangianDifferentials_rank K
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback p).obj (Scheme.Hom.relativeDifferentials (projection K))) 6 :=
    isFiniteLocallyFreeOfRank_pullback p _ 6
  exact MukaiConormalFieldCoordinates.finite_and_finrank_sections K _ 6

end M9Native.MukaiConormalFieldDifferential
