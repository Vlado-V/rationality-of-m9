module

public import M9StacksIntegration.FlagThreeIncidenceChow
public import M9StacksIntegration.ChowLineProperPush
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DegreeHomomorphism

/-!
# Actual base-field kernel points from a nonzero flag-incidence cap

For an actual map between rank-ten bundles, nonvanishing of the genuine
thirtieth Chern cap on its original three-step flag tower forces an
actual base-field point with kernel dimension at least three. The
proper-pushforward and degree versions only use that homomorphisms
preserve zero. The numerical nonvanishing is an explicit input here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.FlagThreeKernelExistence

open Stacks.Chow Stacks.Chow.GenuineChern

variable {X : Scheme.{u}} (K : Type u) [Field K] [IsAlgClosed K]
    (qX : X ⟶ Spec (.of K)) [LocallyOfFiniteType qX]
    (E F : X.Modules)
    [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 10]
    [hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 10]

local instance sourceFiniteLocallyFree :
    SheafOfModules.IsFiniteLocallyFree.{u,u,u} E := hE.isFiniteLocallyFree

local instance dualSourceFiniteLocallyFree :
    SheafOfModules.IsFiniteLocallyFree.{u,u,u} (dualSheaf E) :=
  isFiniteLocallyFree_dualSheaf E inferInstance

local instance projectionProper : IsProper (FlagThreeIncidence.projection E) :=
  FlagTowerProper.isProper_tower 3 (dualSheaf E)

local instance incidenceRank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (FlagThreeIncidence.incidenceBundle E F) 30 :=
  FlagThreeIncidence.incidenceBundle_rank_thirty E F hF

include hE hF

/-- Nonvanishing of the literal incidence top cap gives an actual
base-field point. No extension-field point bound is required. -/
theorem exists_base_field_point_kernel_ge_three_of_topCap_ne_zero
    (v : E ⟶ F) (n : ℤ)
    (α : chowGroup (fieldChowSituation K) (FlagThreeIncidence.projection E ≫ qX) n)
    (hne : chernCap (fieldChowSituation K) 30 (FlagThreeIncidence.projection E ≫ qX)
      (FlagThreeIncidence.incidenceBundle E F) n (Fin.last 30) α ≠ 0) :
    ∃ (p : Spec (.of K) ⟶ X), p ≫ qX = 𝟙 _ ∧
      3 ≤ Module.finrank K (LinearMap.ker (moduleSpecΓFunctor.map
        ((Scheme.Modules.pullback p).map v)).hom) := by
  classical
  by_contra hno
  apply hne
  refine FlagThreeIncidenceChow.topCap_eq_zero_of_base_field_kernel_le_two
    K qX E F v (fun p hp => ?_) n α
  by_contra hle
  apply hno
  exact ⟨p, hp, by omega⟩

/-- The same conclusion follows from a nonzero genuine proper push of
the original top cap. Properness of the flag projection is derived. -/
theorem exists_base_field_point_kernel_ge_three_of_properPush_topCap_ne_zero
    (v : E ⟶ F) (n : ℤ)
    (α : chowGroup (fieldChowSituation K) (FlagThreeIncidence.projection E ≫ qX) n)
    (hne : properChowPushforward (fieldChowSituation K)
      (FlagThreeIncidence.projection E ≫ qX) qX (FlagThreeIncidence.projection E) rfl
      (n - 30)
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper (fieldChowSituation K)
        (FlagThreeIncidence.projection E ≫ qX) qX (FlagThreeIncidence.projection E) rfl
        (n - 30))
      (chernCap (fieldChowSituation K) 30 (FlagThreeIncidence.projection E ≫ qX)
        (FlagThreeIncidence.incidenceBundle E F) n (Fin.last 30) α) ≠ 0) :
    ∃ (p : Spec (.of K) ⟶ X), p ≫ qX = 𝟙 _ ∧
      3 ≤ Module.finrank K (LinearMap.ker (moduleSpecΓFunctor.map
        ((Scheme.Modules.pullback p).map v)).hom) := by
  apply exists_base_field_point_kernel_ge_three_of_topCap_ne_zero K qX E F v n α
  intro hz
  apply hne
  rw [hz, map_zero]

set_option linter.overlappingInstances false in
/-- At grade thirty, a nonzero actual degree of the proper-pushed top
cap is sufficient. This does not assert its numerical nonvanishing.
The finite-type structure is shared with the arbitrary-grade endpoints. -/
theorem exists_base_field_point_kernel_ge_three_of_degree_properPush_topCap_ne_zero
    [IsProper qX] (v : E ⟶ F)
    (α : chowGroup (fieldChowSituation K) (FlagThreeIncidence.projection E ≫ qX) 30)
    (hne : chowDegree (fieldChowSituation K)
      (fieldChowSituation_dimensionFunction_eq_zero K) qX (IsLocalRing.closedPoint K)
      (properChowPushforward (fieldChowSituation K)
        (FlagThreeIncidence.projection E ≫ qX) qX (FlagThreeIncidence.projection E) rfl 0
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper
          (fieldChowSituation K) (FlagThreeIncidence.projection E ≫ qX) qX
          (FlagThreeIncidence.projection E) rfl 0)
        (chernCap (fieldChowSituation K) 30 (FlagThreeIncidence.projection E ≫ qX)
          (FlagThreeIncidence.incidenceBundle E F) 30 (Fin.last 30) α)) ≠ 0) :
    ∃ (p : Spec (.of K) ⟶ X), p ≫ qX = 𝟙 _ ∧
      3 ≤ Module.finrank K (LinearMap.ker (moduleSpecΓFunctor.map
        ((Scheme.Modules.pullback p).map v)).hom) := by
  apply exists_base_field_point_kernel_ge_three_of_topCap_ne_zero
    K qX E F v 30 α
  intro hz
  apply hne
  simp only [hz, map_zero]

end M9Native.FlagThreeKernelExistence
