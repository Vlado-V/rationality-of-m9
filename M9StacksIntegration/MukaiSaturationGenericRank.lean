module

public import M9StacksIntegration.MukaiEvaluationGenericRank

/-!
# Deriving the ranks of the original evaluation saturation and quotient

The original saturation's generic stalk is the original evaluation
image. Torsion freeness on a regular curve supplies local freeness,
and constant-rank descent derives its rank from that original image.
The original torsion-free quotient's rank is then derived by actual
generic short-exact rank additivity. These lemmas apply to the given
evaluation, not to a substituted map with a prescribed rank.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.MukaiSaturationGenericRank

open MukaiSaturationRank MukaiEvaluationSaturation MukaiEvaluationGenericRank

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
variable (f : X ⟶ Spec (.of k))

/-- Any original nonzero section of a torsion-free target makes the
original evaluation's genuine generic rank positive. -/
theorem genericRank_pos_of_section_ne_zero {r : ℕ}
    (E : X.Modules) [E.IsQuasicoherent]
    (hE : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree E)
    (s : Fin r → cohomologyOverField k f E 0) (i : Fin r) (hi : s i ≠ 0) :
    0 < genericRank k f E s := by
  let : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  let : Module.Finite (X.presheaf.stalk (genericPoint X))
      (Stalk (TupleEvaluationFiber.tupleFreeSheaf (X := X) r) (genericPoint X)) :=
    Module.Finite.of_basis (TupleEvaluationFiber.freeStalkBasis r (genericPoint X))
  let φ := MukaiSemiIrreducible.evaluation k f E s
  have hv := h0_generic_germ_ne_zero k f E hE hi
  have hmem : ExteriorEvaluation.h0StalkEvaluation k f E (genericPoint X) (s i) ∈
      LinearMap.range (stalkMap φ (genericPoint X)) :=
    ⟨TupleEvaluationFiber.freeStalkBasis r (genericPoint X) i,
      evaluation_stalk_basis k f E s (genericPoint X) i⟩
  by_contra hn
  have hz : genericRank k f E s = 0 := Nat.eq_zero_of_not_pos hn
  have hbot : LinearMap.range (stalkMap φ (genericPoint X)) = ⊥ :=
    Submodule.finrank_eq_zero.mp hz
  exact hv (by simpa only [hbot,Submodule.mem_bot] using hmem)

section Ranks

variable {r : ℕ} (E : X.Modules) [E.IsQuasicoherent]
variable [hE : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E]
variable (s : Fin r → cohomologyOverField k f E 0)
variable [(cokernel (MukaiSemiIrreducible.evaluation k f E s)).IsQuasicoherent]

/-- The actual saturation has the rank of the original evaluation
image, obtained from its proved generic-stalk equality. -/
theorem saturation_rank_of_genericRank_eq
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1) (d : ℕ)
    (hd : genericRank k f E s = d) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (saturation (MukaiSemiIrreducible.evaluation k f E s)) d := by
  let φ := MukaiSemiIrreducible.evaluation k f E s
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  let : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X E
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (saturation φ) :=
    saturation_isFiniteLocallyFree φ hreg hdim hE
  let : (saturation φ).IsCoherent := saturation_isCoherent φ
  let : (saturation φ).IsFiniteType := _root_.IsCoherent.toIsFiniteType _
  have hdimS : Module.finrank (X.presheaf.stalk (genericPoint X))
      (Stalk (saturation φ) (genericPoint X)) = d :=
    (finrank_saturation_generic_eq_finrank_range φ).trans hd
  have hfr : Scheme.Modules.fiberRank (saturation φ) (genericPoint X) = d :=
    (Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk (saturation φ)).trans hdimS
  exact Scheme.Modules.isFiniteLocallyFreeOfRank_of_fiberRank_eq
    (saturation φ) d (genericPoint X) hfr

/-- The original torsion-free quotient has the complementary derived
rank, using the actual original saturation short exact sequence. -/
theorem quotient_rank_of_genericRank_eq
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1) (n d : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E n]
    (hd : genericRank k f E s = d) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (torsionFreeQuotient (MukaiSemiIrreducible.evaluation k f E s)) (n - d) := by
  let φ := MukaiSemiIrreducible.evaluation k f E s
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  let : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X E
  let : (saturation φ).IsCoherent := saturation_isCoherent φ
  let : (torsionFreeQuotient φ).IsCoherent := torsionFreeQuotient_isCoherent φ
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (saturation φ) d :=
    saturation_rank_of_genericRank_eq k f E s hreg hdim d hd
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (torsionFreeQuotient φ) :=
    torsionFreeQuotient_isFiniteLocallyFree φ hreg hdim hE
  have hadd := Scheme.Modules.fiberRank_genericPoint_add_of_shortExact
    (ShortComplex.mk (inclusion φ) (projection φ) (kernel.condition (projection φ)))
    (sequence_shortExact φ)
  have hEn := Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank E n (genericPoint X)
  have hSd := Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank
    (saturation φ) d (genericPoint X)
  have hQ : Scheme.Modules.fiberRank (torsionFreeQuotient φ) (genericPoint X) = n - d := by
    change Scheme.Modules.fiberRank E (genericPoint X) =
      Scheme.Modules.fiberRank (saturation φ) (genericPoint X) +
        Scheme.Modules.fiberRank (torsionFreeQuotient φ) (genericPoint X) at hadd
    rw [hEn,hSd] at hadd
    omega
  exact Scheme.Modules.isFiniteLocallyFreeOfRank_of_fiberRank_eq
    (torsionFreeQuotient φ) (n - d) (genericPoint X) hQ

end Ranks

end M9Native.MukaiSaturationGenericRank
