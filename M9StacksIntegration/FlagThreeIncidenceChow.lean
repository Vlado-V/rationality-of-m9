module

public import M9StacksIntegration.FlagThreeIncidenceSection
public import M9StacksIntegration.UnitSubbundleChow

/-!
# Integral Chow vanishing of the actual rank-thirty flag incidence bundle

An actual base-field kernel bound for an actual rank-ten bundle map makes
its original flag-incidence section nonzero at the actual base-field
points. The checked finite-type/closed-point/cokernel geometry and native
Whitney formula therefore annihilate every actual integral Chow class
under its thirtieth Chern cap. No condition over extension-field points,
expected codimension, cycle realization, or Schur value is assumed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.FlagThreeIncidenceChow

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

theorem topCap_eq_zero_of_base_field_kernel_le_two
    (v : E ⟶ F)
    (hker : ∀ (p : Spec (.of K) ⟶ X), p ≫ qX = 𝟙 _ →
      Module.finrank K (LinearMap.ker (moduleSpecΓFunctor.map
        ((Scheme.Modules.pullback p).map v)).hom) ≤ 2)
    (n : ℤ)
    (α : chowGroup (fieldChowSituation K) (FlagThreeIncidence.projection E ≫ qX) n) :
    chernCap (fieldChowSituation K) 30 (FlagThreeIncidence.projection E ≫ qX)
      (FlagThreeIncidence.incidenceBundle E F) n (Fin.last 30) α = 0 := by
  haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (FlagThreeIncidence.incidenceBundle E F) (29+1) := by
    change SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (FlagThreeIncidence.incidenceBundle E F) 30
    exact FlagThreeIncidence.incidenceBundle_rank_thirty E F hF
  refine UnitSubbundleChow.topCap_eq_zero_of_base_field_nonvanishing
    (fieldChowSituation K) (FlagThreeIncidence.projection E ≫ qX)
    (FlagThreeIncidence.projection E ≫ qX) (FlagThreeIncidence.incidenceBundle E F) 29
    (CurriedHomSection.curriedMap (FlagThreeIncidence.restriction E v)) ?_ n α
  intro p hp
  apply FlagThreeIncidence.fieldPoint_incidenceSection_ne_zero E hE v K p
  exact hker (p ≫ FlagThreeIncidence.projection E) (by simpa only [Category.assoc] using hp)

end M9Native.FlagThreeIncidenceChow
