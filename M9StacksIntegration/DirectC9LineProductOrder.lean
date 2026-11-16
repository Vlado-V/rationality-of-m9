module

public import M9StacksIntegration.DirectC9GraphRootEvaluation
public import M9StacksIntegration.GradedCapSegreComparison

/-!
# Ordering the actual line-cap factors for the C9 filtration

All commutation takes place in the proved commutative subring generated
by the original line caps and is carried to the original cap ring by
its genuine inclusion. No global cap-ring commutativity is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.CurvePower

universe u

namespace M9Native.DirectC9LineProductOrder

open Stacks.Chow ChowCapWords GradedLineCapSubring GradedCapSegreComparison
open DirectC9GraphRootEvaluation

section Generic

variable (A : ChowSituation.{u}) {X : Scheme.{u}} (s : X ⟶ A.S) [LocallyOfFiniteType s]

def lineProduct (L : List (InvertibleLine X)) : GradedCapFamily (chowGroup A s) :=
  (L.map (fun M => 1 + lineFamily A s M)).prod

theorem inclusion_lineProduct (L : List (InvertibleLine X)) :
    inclusion A s ((L.map (fun M => 1 + lineRoot A s M)).prod) = lineProduct A s L := by
  induction L with
  | nil => exact (inclusion A s).map_one
  | cons M L ih =>
      change inclusion A s ((1 + lineRoot A s M) *
        (L.map (fun N => 1 + lineRoot A s N)).prod) =
          (1 + lineFamily A s M) * lineProduct A s L
      rw [(inclusion A s).map_mul, ih]
      rfl

theorem lineProduct_append (L M : List (InvertibleLine X)) :
    lineProduct A s (L ++ M) = lineProduct A s L * lineProduct A s M := by
  simp only [lineProduct, List.map_append, List.prod_append]

theorem lineProduct_replicate (L : InvertibleLine X) (n : ℕ) :
    lineProduct A s (List.replicate n L) = (1 + lineFamily A s L) ^ n := by
  simp only [lineProduct, List.map_replicate, List.prod_replicate]

theorem lineProduct_reverse (L : List (InvertibleLine X)) :
    lineProduct A s L.reverse = lineProduct A s L := by
  calc
    lineProduct A s L.reverse =
        inclusion A s ((L.reverse.map (fun M => 1 + lineRoot A s M)).prod) :=
      (inclusion_lineProduct A s L.reverse).symm
    _ = inclusion A s ((L.map (fun M => 1 + lineRoot A s M)).prod) := by
      rw [List.map_reverse, List.prod_reverse]
    _ = lineProduct A s L := inclusion_lineProduct A s L

theorem lineProduct_commute (L M : List (InvertibleLine X)) :
    Commute (lineProduct A s L) (lineProduct A s M) := by
  change lineProduct A s L * lineProduct A s M = lineProduct A s M * lineProduct A s L
  rw [← inclusion_lineProduct A s L, ← inclusion_lineProduct A s M,
    ← (inclusion A s).map_mul, ← (inclusion A s).map_mul]
  exact congrArg (inclusion A s) (mul_comm _ _)

end Generic

section Power

variable {k : Type u} [Field k] (C : Over (Spec (.of k))) [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)

theorem quotientLineAt_range :
    (List.range 9).map (quotientLineAt C c₀) = List.ofFn (quotientLine C c₀) := by
  have h := List.ofFn_getElem_eq_map (List.range 9) (quotientLineAt C c₀)
  have hcast : ∀ {n m : ℕ} (e : n = m) (i : Fin n), (Fin.cast e i).val = i.val := by
    intro n m e i
    cases e
    rfl
  have h' : List.ofFn (fun i : Fin 9 => quotientLineAt C c₀ i.val) =
      (List.range 9).map (quotientLineAt C c₀) := by
    simpa only [List.length_range, List.getElem_range, hcast] using h
  have hf : (fun i : Fin 9 => quotientLineAt C c₀ i.val) = quotientLine C c₀ := by
    funext i
    exact quotientLineAt_of_lt C c₀ i.val i.isLt
  rw [hf] at h'
  exact h'.symm

theorem graphLines_eq_reverse_ofFn :
    graphLines C c₀ = (List.ofFn (quotientLine C c₀)).reverse ++
      List.replicate 9 (normalizationLine C c₀) := by
  rw [graphLines, List.map_reverse, quotientLineAt_range]

variable (A : ChowSituation.{u}) (s : (power C 9).left ⟶ A.S) [LocallyOfFiniteType s]

theorem graphLines_product_order :
    (1 + lineFamily A s (normalizationLine C c₀)) ^ 9 *
        ChowWhitneyLineTower.orderedPrefix
          (fun a : Fin 9 => 1 + lineFamily A s (quotientLine C c₀ a)) 9 le_rfl =
      lineProduct A s (graphLines C c₀) := by
  let N := List.replicate 9 (normalizationLine C c₀)
  let K := List.ofFn (quotientLine C c₀)
  have hn : lineProduct A s N = (1 + lineFamily A s (normalizationLine C c₀)) ^ 9 :=
    lineProduct_replicate A s (normalizationLine C c₀) 9
  have hk : ChowWhitneyLineTower.orderedPrefix
      (fun a : Fin 9 => 1 + lineFamily A s (quotientLine C c₀ a)) 9 le_rfl =
        lineProduct A s K := by
    rw [orderedPrefix_eq_ofFn_prod]
    simp only [lineProduct, K, List.map_ofFn, Function.comp_def]
  calc
    (1 + lineFamily A s (normalizationLine C c₀)) ^ 9 *
        ChowWhitneyLineTower.orderedPrefix
          (fun a : Fin 9 => 1 + lineFamily A s (quotientLine C c₀ a)) 9 le_rfl =
        lineProduct A s N * lineProduct A s K := by rw [hn, hk]
    _ = lineProduct A s K * lineProduct A s N := (lineProduct_commute A s N K).eq
    _ = lineProduct A s K.reverse * lineProduct A s N :=
      congrArg (fun a => a * lineProduct A s N) (lineProduct_reverse A s K).symm
    _ = lineProduct A s (graphLines C c₀) := by
      rw [graphLines_eq_reverse_ofFn]
      exact (lineProduct_append A s K.reverse N).symm

end Power

end M9Native.DirectC9LineProductOrder
