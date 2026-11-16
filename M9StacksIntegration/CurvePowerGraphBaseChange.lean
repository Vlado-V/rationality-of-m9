module

public import M9StacksIntegration.CurvePowerGraphCartier

/-!
# Literal graph base change under native curve-power reindexing

Extending a reindexing by an unchanged first curve coordinate is the
original native family base-change map. Pulling back the actual graph
class therefore gives the actual graph class of the composed point.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory Stacks.CurvePower

universe u

namespace M9Native.CurvePowerGraphBaseChange

variable {S : Scheme.{u}} (C : Over S)

def extendIndex {m n : ℕ} (σ : Fin m → Fin n) : Fin (m + 1) → Fin (n + 1) :=
  Fin.cases 0 (fun i => (σ i).succ)

theorem reindex_extend_left {m n : ℕ} (σ : Fin m → Fin n) :
    (reindex C (extendIndex σ)).left =
      Stacks.Hilbert.familyBaseChangeMap C (reindex C σ) := by
  refine pullback.hom_ext ?_ ?_
  · change (reindex C (extendIndex σ) ≫ fst C (power C m)).left = _
    rw [← coord_zero, reindex_coord]
    change (fst C (power C n)).left = _
    simp [Stacks.Hilbert.familyBaseChangeMap]
  · have hm : reindex C (extendIndex σ) ≫ snd C (power C m) =
        snd C (power C n) ≫ reindex C σ := by
      apply Stacks.CurvePower.hom_ext m
      intro i
      simp only [Category.assoc, ← coord_succ, reindex_coord, extendIndex, Fin.cases_succ]
    change (reindex C (extendIndex σ) ≫ snd C (power C m)).left = _
    rw [hm]
    simp [Stacks.Hilbert.familyBaseChangeMap]

theorem graphSection_comp_hom (m : ℕ) (y : power C m ⟶ C) :
    CurvePowerGraphCartier.graphSection C m y ≫ (power C (m + 1)).hom =
      (power C m).hom := by
  change Stacks.Hilbert.pointGraph C (power C m) y ≫
    (pullback.fst C.hom (power C m).hom ≫ C.hom) = _
  rw [pullback.condition, ← Category.assoc, Stacks.Hilbert.pointGraph_comp_snd,
    Category.id_comp]

variable [IsSeparated C.hom] [SmoothOfRelativeDimension 1 C.hom]

theorem graphClass_pullback_reindex_extend {m n : ℕ} (σ : Fin m → Fin n)
    (y : power C m ⟶ C) :
    Stacks.Picard.schemePullbackClass (reindex C (extendIndex σ)).left
        (CurvePowerGraphCartier.graphClass C m y) =
      CurvePowerGraphCartier.graphClass C n (reindex C σ ≫ y) := by
  have : IsClosedImmersion (Stacks.Hilbert.pointGraph C (power C m) y) :=
    Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated C (power C m) y
  apply Stacks.Hilbert.HilbertFamily.schemePullbackClass_picardClass
    (GraphNormalPicard.graphFamily C (power C m) y)
    (GraphNormalPicard.graphFamily C (power C n) (reindex C σ ≫ y))
  rw [reindex_extend_left]
  exact (Stacks.Hilbert.pointIdeal_comap_familyBaseChangeMap C (reindex C σ) y).symm

end M9Native.CurvePowerGraphBaseChange
