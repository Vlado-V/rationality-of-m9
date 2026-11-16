module

public import M9StacksIntegration.DirectC9InitialChern
public import M9StacksIntegration.DirectC9LineProductOrder
public import M9StacksIntegration.DirectC9MovingChern

/-!
# The actual E18 Chern family is the actual evaluated line product

The initial free-line tensor isomorphism and the original nine ordinary
short exact moving rows supply every Chern identity used here. The
finite factors are reordered only in the proved line-generated subring.
No Chern-product, root, coefficient or nonzero hypothesis is supplied.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.CurvePower MvPolynomial

universe u

namespace M9Native.DirectC9FullChern

open Stacks.Chow Stacks.Chow.GenuineChern GradedLineCapSubring GradedCapVirtualSchur
open CurvePowerChowFunctional CurvePowerGraphSchurPolynomial
open CurvePowerLinePolynomialTrace LinePolynomialEvaluation
open DirectC9GraphRootEvaluation DirectC9LineProductOrder GradedCapSegreComparison

def graphTotalPolynomial : MvPolynomial (Letter 9) ℤ :=
  (graphRootPolynomials.map (fun p => 1 + p)).prod

section Polynomial

variable (k : Type u) [Field k] (C : Over (Spec (.of k))) [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)

theorem graphTotalPolynomial_evaluation :
    nativeEvaluation (fieldChowSituation k) (power C 9).hom (variableLine k C c₀ 9)
      graphTotalPolynomial = lineProduct (fieldChowSituation k) (power C 9).hom (graphLines C c₀) := by
  let E := evaluation (fieldChowSituation k) (power C 9).hom (variableLine k C c₀ 9)
  have hp : E graphTotalPolynomial =
      ((graphRootPolynomials.map E).map (fun r => 1 + r)).prod := by
    calc
      E graphTotalPolynomial =
          ((graphRootPolynomials.map (fun p => 1 + p)).map E).prod :=
        E.toMonoidHom.map_list_prod (graphRootPolynomials.map (fun p => 1 + p))
      _ = ((graphRootPolynomials.map E).map (fun r => 1 + r)).prod := by
        simp only [List.map_map, Function.comp_def]
        apply congrArg List.prod
        apply List.map_congr_left
        intro p hp
        calc
          E (1 + p) = E 1 + E p := E.toAddMonoidHom.map_add 1 p
          _ = 1 + E p := congrArg (fun r => r + E p) E.map_one
  change inclusion (fieldChowSituation k) (power C 9).hom (E graphTotalPolynomial) = _
  rw [hp, DirectC9GraphRootEvaluation.graphRootPolynomials_evaluation C c₀]
  simpa only [List.map_map, Function.comp_def] using
    inclusion_lineProduct (fieldChowSituation k) (power C 9).hom (graphLines C c₀)

end Polynomial

section Chern

variable (k : Type u) [Field k] [IsAlgClosed k] (C : Over (Spec (.of k)))
  [IsCurve k C.hom] [IsProper C.hom] [Smooth C.hom]

local instance original_relativeDimension : SmoothOfRelativeDimension 1 C.hom :=
  DirectC9FibreGeometry.original_relativeDimension k C

variable (c₀ : power C 0 ⟶ C) (hg : genus C.hom = 9)

include hg

theorem E18_chernFamily_eq_graphLines (A : ChowSituation.{u})
    (s : (power C 9).left ⟶ A.S) [LocallyOfFiniteType s] :
    @chernFamily A (power C 9).left s _ (DirectC9Bundles.E18 k C c₀) 18
      (DirectC9Bundles.E18_rank k C c₀ hg) = lineProduct A s (graphLines C c₀) := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (DirectC9Bundles.E18 k C c₀) 18 := DirectC9Bundles.E18_rank k C c₀ hg
  calc
    chernFamily A s (DirectC9Bundles.E18 k C c₀) 18 =
        @chernFamily A (power C 9).left s _
          (DirectC9Bundles.movingPushforward k C c₀ 0 (Nat.zero_le 9)) 9
          (by simpa using DirectC9Bundles.movingPushforward_rank k C c₀ hg 0 (Nat.zero_le 9)) *
            ChowWhitneyLineTower.orderedPrefix
              (fun a : Fin 9 => 1 + lineFamily A s (quotientLine C c₀ a)) 9 le_rfl :=
      DirectC9MovingChern.E18_chernFamily_eq_moving_product k C c₀ hg A s
    _ = (1 + lineFamily A s (normalizationLine C c₀)) ^ 9 *
        ChowWhitneyLineTower.orderedPrefix
          (fun a : Fin 9 => 1 + lineFamily A s (quotientLine C c₀ a)) 9 le_rfl :=
      congrArg (fun a : GradedCapFamily (chowGroup A s) =>
        a * ChowWhitneyLineTower.orderedPrefix
          (fun j : Fin 9 => 1 + lineFamily A s (quotientLine C c₀ j)) 9 le_rfl)
        (DirectC9InitialChern.initial_chernFamily k C c₀ hg A s)
    _ = lineProduct A s (graphLines C c₀) := graphLines_product_order C c₀ A s

theorem E18_chernFamily_eq_polynomial :
    @chernFamily (fieldChowSituation k) (power C 9).left (power C 9).hom _
      (DirectC9Bundles.E18 k C c₀) 18 (DirectC9Bundles.E18_rank k C c₀ hg) =
      nativeEvaluation (fieldChowSituation k) (power C 9).hom (variableLine k C c₀ 9)
        graphTotalPolynomial :=
  (E18_chernFamily_eq_graphLines k C c₀ hg (fieldChowSituation k) (power C 9).hom).trans
    (graphTotalPolynomial_evaluation k C c₀).symm

theorem E18_homComponent_eq_elementary (A : ChowSituation.{u})
    (s : (power C 9).left ⟶ A.S) [LocallyOfFiniteType s] (i : ℕ) :
    homComponent i (@chernFamily A (power C 9).left s _ (DirectC9Bundles.E18 k C c₀) 18
      (DirectC9Bundles.E18_rank k C c₀ hg)) =
      inclusion A s (CurvePowerRootChern.elementary ((graphLines C c₀).map (lineRoot A s)) i) := by
  rw [E18_chernFamily_eq_graphLines k C c₀ hg A s]
  exact homComponent_line_list_product A s (graphLines C c₀) i

theorem E18_inverseComponent_eq_segre (A : ChowSituation.{u})
    (s : (power C 9).left ⟶ A.S) [LocallyOfFiniteType s] (i : ℕ) :
    homComponent i (@inverseFamily A (power C 9).left s _ (DirectC9Bundles.E18 k C c₀) 18
      (DirectC9Bundles.E18_rank k C c₀ hg)) =
      inclusion A s (CurvePowerRootChern.segreCoefficient ((graphLines C c₀).map (lineRoot A s)) i) := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (DirectC9Bundles.E18 k C c₀) 18 := DirectC9Bundles.E18_rank k C c₀ hg
  apply inverseComponent_eq_segre_of_coefficients A s (DirectC9Bundles.E18 k C c₀) 18
    ((graphLines C c₀).map (lineRoot A s)) i _ i le_rfl
  intro j hj
  exact E18_homComponent_eq_elementary k C c₀ hg A s j

end Chern

end M9Native.DirectC9FullChern
