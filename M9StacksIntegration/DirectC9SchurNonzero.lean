module

public import M9StacksIntegration.DirectC9FullChern
public import M9StacksIntegration.DirectC9VirtualChern

/-!
# The original actual C9 virtual Schur operator has nonzero degree

Every line product and unit-row identity comes from the actual ordinary
bundles and their proved short exact rows. Finite inverse coefficients
identify the original virtual operator with the original named-line
Schur operator whose integral Chow degree was computed. No Chern,
coefficient, product, realization or nonzero premise is supplied.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.CurvePower

universe u

namespace M9Native.DirectC9SchurNonzero

open Stacks.Chow GradedLineCapSubring GradedCapVirtualSchur GradedCapSegreComparison
open DirectC9GraphRootEvaluation GradedCapTopTrace

variable (k : Type u) [Field k] [IsAlgClosed k] (C : Over (Spec (.of k)))
  [IsCurve k C.hom] [IsProper C.hom] [Smooth C.hom]

local instance original_relativeDimension : SmoothOfRelativeDimension 1 C.hom :=
  DirectC9FibreGeometry.original_relativeDimension k C

variable (c₀ : power C 0 ⟶ C) (hg : genus C.hom = 9)

include hg

theorem virtualComponent_eq_segre (A : ChowSituation.{u})
    (s : (power C 9).left ⟶ A.S) [LocallyOfFiniteType s] (i : ℕ) :
    @virtualComponent A (power C 9).left s _
      (DirectC9Bundles.F10 k C c₀) (DirectC9Bundles.E10 k C c₀) 10 10
      (DirectC9Bundles.F10_rank k C c₀) (DirectC9Bundles.E10_rank k C c₀ hg) i =
      inclusion A s (CurvePowerRootChern.segreCoefficient
        ((graphLines C c₀).map (lineRoot A s)) i) := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (DirectC9Bundles.E10 k C c₀) 10 :=
    DirectC9Bundles.E10_rank k C c₀ hg
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (DirectC9Bundles.F10 k C c₀) 10 :=
    DirectC9Bundles.F10_rank k C c₀
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (DirectC9Bundles.E18 k C c₀) 18 :=
    DirectC9Bundles.E18_rank k C c₀ hg
  dsimp only [virtualComponent]
  rw [DirectC9VirtualChern.virtualF10_E10_eq_inverseE18 k C c₀ hg A s]
  exact DirectC9FullChern.E18_inverseComponent_eq_segre k C c₀ hg A s i

theorem virtualSchur_eq_graphLines (A : ChowSituation.{u})
    (s : (power C 9).left ⟶ A.S) [LocallyOfFiniteType s] :
    schur333 (@virtualFamily A (power C 9).left s _
      (DirectC9Bundles.F10 k C c₀) (DirectC9Bundles.E10 k C c₀) 10 10
      (DirectC9Bundles.F10_rank k C c₀) (DirectC9Bundles.E10_rank k C c₀ hg)) =
      inclusion A s (CurvePowerRootChern.segreSchurMatrix
        ((graphLines C c₀).map (lineRoot A s))).det := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (DirectC9Bundles.E10 k C c₀) 10 :=
    DirectC9Bundles.E10_rank k C c₀ hg
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (DirectC9Bundles.F10 k C c₀) 10 :=
    DirectC9Bundles.F10_rank k C c₀
  apply schur333_eq_image_segreDet_of_components A s _ ((graphLines C c₀).map (lineRoot A s))
  intro i hi hi5
  exact virtualComponent_eq_segre k C c₀ hg A s i

attribute [local irreducible] GradedCapTopTrace.topTrace

set_option backward.isDefEq.respectTransparency true in
theorem virtualSchur_topTrace :
    topTrace k (power C 9).hom 9
      (schur333 (@virtualFamily (fieldChowSituation k) (power C 9).left (power C 9).hom _
        (DirectC9Bundles.F10 k C c₀) (DirectC9Bundles.E10 k C c₀) 10 10
        (DirectC9Bundles.F10_rank k C c₀) (DirectC9Bundles.E10_rank k C c₀ hg))) = 15240960 := by
  have hc := (isCurve_iff k C.hom).mp (inferInstance : IsCurve k C.hom)
  let : IsVariety k C.hom := hc.1
  have hs := virtualSchur_eq_graphLines k C c₀ hg (fieldChowSituation k) (power C 9).hom
  have ht := graphLinesSchur_topTrace (k := k) C c₀ hc.2 hg
  exact (congrArg (topTrace k (power C 9).hom 9) hs).trans ht

theorem virtualSchur_ne_zero :
    schur333 (@virtualFamily (fieldChowSituation k) (power C 9).left (power C 9).hom _
      (DirectC9Bundles.F10 k C c₀) (DirectC9Bundles.E10 k C c₀) 10 10
      (DirectC9Bundles.F10_rank k C c₀) (DirectC9Bundles.E10_rank k C c₀ hg)) ≠ 0 := by
  intro hz
  have ht := virtualSchur_topTrace k C c₀ hg
  rw [hz, map_zero] at ht
  norm_num at ht

end M9Native.DirectC9SchurNonzero
