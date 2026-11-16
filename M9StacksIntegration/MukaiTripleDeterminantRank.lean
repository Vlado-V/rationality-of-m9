module

public import M9StacksIntegration.MukaiEvaluationGenericRank
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank

/-!
# Actual determinant vanishing and ranks of original triple evaluation

On a regular integral curve, a nonmonic native triple evaluation has zero
actual third exterior H0 value. Conversely, a nonzero actual determinant
value gives a genuine sheaf monomorphism. The zero determinant has fibre
rank at most two at every original point. No independence, completeness,
or semi-irreducibility premise is needed for these implications.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Module

universe u v

namespace M9Native.MukaiTripleDeterminantRank

section Linear

variable {K : Type u} {M : Type v} [Field K] [AddCommGroup M] [Module K M]

/-- Actual independence gives a nonzero actual exterior product over a field. -/
theorem wedge_ne_zero_of_linearIndependent {r : ℕ} (s : Fin r → M)
    (hs : LinearIndependent K s) : exteriorPower.ιMulti K r s ≠ 0 := by
  let t : Set.powersetCard (Fin r) r :=
    Set.powersetCard.ofFinEmbEquiv
      (OrderEmbedding.ofStrictMono (id : Fin r → Fin r) strictMono_id)
  have hn := LinearIndependent.ne_zero t
    (exteriorPower.ιMulti_family_linearIndependent_field (n := r) hs)
  simpa [t, exteriorPower.ιMulti_family] using hn

end Linear

open MukaiSaturationRank TupleEvaluationFiber

variable {X : Scheme.{u}} (k : Type u) [Field k]
  (f : X ⟶ Spec (.of k)) (E : X.Modules)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]

/-- A zero actual determinant section gives rank at most two on every genuine residue fibre. -/
theorem mapRankAt_le_two_of_lambda_eq_zero
    (s : Fin 3 → cohomologyOverField k f E 0)
    (hdet : ExteriorEvaluation.lambda k f E 3 (exteriorPower.ιMulti k 3 s) = 0)
    (x : X) :
    MukaiSemiIrreducible.mapRankAt (MukaiSemiIrreducible.evaluation k f E s) x ≤ 2 := by
  letI := residueAlgebra x
  letI : Module.Finite (X.residueField x) (Fiber E x) := fiberFinite E 3 x
  rw [mapRankAt_evaluation_eq_finrank_tupleMap]
  let a := tupleMap k f E s x
  have hle : Module.finrank (X.residueField x) (LinearMap.range a) ≤ 3 :=
    a.finrank_range_le.trans_eq (by simp)
  have hne : Module.finrank (X.residueField x) (LinearMap.range a) ≠ 3 := by
    intro he
    have hrange : LinearMap.range a = Submodule.span (X.residueField x)
        (Set.range (fun i => sectionValue k f E x (s i))) :=
      (Pi.basisFun (X.residueField x) (Fin 3)).constr_range (X.residueField x)
    have hdim : Fintype.card (Fin 3) = Module.finrank (X.residueField x)
        (Submodule.span (X.residueField x)
          (Set.range (fun i => sectionValue k f E x (s i)))) := by
      rw [← hrange, he]
      rfl
    have hli : LinearIndependent (X.residueField x)
        (fun i => sectionValue k f E x (s i)) :=
      linearIndependent_iff_card_eq_finrank_span.mpr hdim
    apply wedge_ne_zero_of_linearIndependent _ hli
    exact ExteriorEvaluation.wedge_fiber_eq_zero_of_lambda_eq_zero
      k f x (X.residueField x) E 3 s hdet
  change Module.finrank (X.residueField x) (LinearMap.range a) ≤ 2
  omega

section IntegralCurve

variable [IsIntegral X] (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)
include hreg hdim

/-- Nonzero actual determinant forces the original triple evaluation to be monic. -/
theorem evaluation_mono_of_lambda_ne_zero
    (s : Fin 3 → cohomologyOverField k f E 0)
    (hdet : ExteriorEvaluation.lambda k f E 3 (exteriorPower.ιMulti k 3 s) ≠ 0) :
    Mono (MukaiSemiIrreducible.evaluation k f E s) := by
  letI : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  let D : X.Modules := Scheme.Modules.exteriorPower E (3 : ℤ)
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D 1 := by
    simpa [D] using Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower E 3 3
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} D :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree D 1
  letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  letI : D.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X D
  letI : D.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree D
  have hDT : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree D :=
    (isTorsionFree_iff_isFiniteLocallyFree hreg hdim D).mpr inferInstance
  have hη := h0_generic_germ_ne_zero k f D hDT hdet
  have hw : exteriorPower.ιMulti (X.presheaf.stalk (genericPoint X)) 3
      (fun i => ExteriorEvaluation.h0StalkEvaluation k f E (genericPoint X) (s i)) ≠ 0 := by
    intro hz
    apply hη
    apply (ExteriorEvaluation.stalkComparison E 3 (genericPoint X)).injective
    exact (ExteriorEvaluation.lambda_germ_ιMulti k f E 3 (genericPoint X) s).trans
      (hz.trans (map_zero _).symm)
  have hli : LinearIndependent (X.presheaf.stalk (genericPoint X))
      (fun i => ExteriorEvaluation.h0StalkEvaluation k f E (genericPoint X) (s i)) := by
    by_contra hn
    exact hw (AlternatingMap.map_linearDependent
      (exteriorPower.ιMulti (X.presheaf.stalk (genericPoint X)) 3) _ hn)
  have hfull : MukaiEvaluationGenericRank.genericRank k f E s = 3 := by
    change Module.finrank (X.presheaf.stalk (genericPoint X))
      (LinearMap.range (stalkMap (MukaiSemiIrreducible.evaluation k f E s) (genericPoint X))) = 3
    rw [← range_stalkTupleMap_eq_range_evaluation k f E s (genericPoint X), range_stalkTupleMap]
    simpa only [Set.finrank, Fintype.card_fin] using
      (linearIndependent_iff_card_eq_finrank_span.mp hli).symm
  exact MukaiEvaluationGenericRank.evaluation_mono_of_genericRank_eq k f E s hreg hdim hfull

/-- Thus nonmonicity supplies genuine determinant vanishing, not a supplied hyperplane condition. -/
theorem lambda_eq_zero_of_not_mono
    (s : Fin 3 → cohomologyOverField k f E 0)
    (hn : ¬ Mono (MukaiSemiIrreducible.evaluation k f E s)) :
    ExteriorEvaluation.lambda k f E 3 (exteriorPower.ιMulti k 3 s) = 0 := by
  by_contra hdet
  exact hn (evaluation_mono_of_lambda_ne_zero k f E hreg hdim s hdet)

end IntegralCurve

end M9Native.MukaiTripleDeterminantRank
