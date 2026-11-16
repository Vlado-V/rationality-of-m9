module

public import M9StacksIntegration.MukaiGenericMono

/-!
# The generic rank alternatives of the original evaluation map

The generic rank is computed from the actual local-ring stalk map of
the original finite free evaluation source. Its rank is bounded by the
number of original sections. Full generic source rank implies an
actual sheaf monomorphism by torsion freeness of the genuine free
source. Consequently a nonmonic original triple has generic rank at
most two; no desired evaluation rank is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.MukaiEvaluationGenericRank

open MukaiSaturationRank

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
variable (f : X ⟶ Spec (.of k))

/-- The genuine rank of the original evaluation at the original
generic local-ring stalk. -/
def genericRank {r : ℕ} (E : X.Modules) (s : Fin r → cohomologyOverField k f E 0) : ℕ :=
  Module.finrank (X.presheaf.stalk (genericPoint X))
    (LinearMap.range (stalkMap (MukaiSemiIrreducible.evaluation k f E s) (genericPoint X)))

private theorem freeSourceGeneric_finrank (r : ℕ) :
    Module.finrank (X.presheaf.stalk (genericPoint X))
      (Stalk (TupleEvaluationFiber.tupleFreeSheaf (X := X) r) (genericPoint X)) = r := by
  exact (Module.finrank_eq_card_basis (TupleEvaluationFiber.freeStalkBasis r (genericPoint X))).trans
    (by simp)

/-- The original finite free source bounds the actual generic rank. -/
theorem genericRank_le {r : ℕ} (E : X.Modules)
    (s : Fin r → cohomologyOverField k f E 0) : genericRank k f E s ≤ r := by
  let : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  let : Module.Finite (X.presheaf.stalk (genericPoint X))
      (Stalk (TupleEvaluationFiber.tupleFreeSheaf (X := X) r) (genericPoint X)) :=
    Module.Finite.of_basis (TupleEvaluationFiber.freeStalkBasis r (genericPoint X))
  exact (stalkMap (MukaiSemiIrreducible.evaluation k f E s) (genericPoint X)).finrank_range_le.trans_eq
    (freeSourceGeneric_finrank r)

/-- Full genuine generic rank forces the original sheaf evaluation
itself to be monic. -/
theorem evaluation_mono_of_genericRank_eq {r : ℕ} (E : X.Modules)
    (s : Fin r → cohomologyOverField k f E 0)
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)
    (hfull : genericRank k f E s = r) : Mono (MukaiSemiIrreducible.evaluation k f E s) := by
  let : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  let A := TupleEvaluationFiber.tupleFreeSheaf (X := X) r
  let : Module.Finite (X.presheaf.stalk (genericPoint X)) (Stalk A (genericPoint X)) :=
    Module.Finite.of_basis (TupleEvaluationFiber.freeStalkBasis r (genericPoint X))
  let φ := MukaiSemiIrreducible.evaluation k f E s
  have hd := (stalkMap φ (genericPoint X)).finrank_range_add_finrank_ker
  have hsource := freeSourceGeneric_finrank (X := X) r
  have hkzero : Module.finrank (X.presheaf.stalk (genericPoint X))
      (LinearMap.ker (stalkMap φ (genericPoint X))) = 0 := by
    change Module.finrank (X.presheaf.stalk (genericPoint X))
      (LinearMap.range (stalkMap φ (genericPoint X))) = r at hfull
    rw [hfull,hsource] at hd
    omega
  have hinj : Function.Injective (stalkMap φ (genericPoint X)) :=
    LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hkzero)
  have hA : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} A r :=
    SheafOfModules.isFiniteLocallyFreeOfRank_free_of_equiv (ULift.{u} (Fin r)) r Equiv.ulift
  let hAF : SheafOfModules.IsFiniteLocallyFree.{u,u,u} A := hA.isFiniteLocallyFree
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  let : A.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X A
  let : A.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree A
  have hAT : Stacks.AlgebraicGeometry.ReflexiveModules.IsTorsionFree A :=
    (isTorsionFree_iff_isFiniteLocallyFree hreg hdim A).mpr hAF
  exact MukaiGenericMono.mono_of_generic_stalkMap_injective hAT φ hinj

/-- A nonmonic original evaluation has genuinely smaller generic
rank, derived from its original finite free source. -/
theorem genericRank_le_pred_of_not_mono {r : ℕ} (E : X.Modules)
    (s : Fin r → cohomologyOverField k f E 0)
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)
    (hn : ¬ Mono (MukaiSemiIrreducible.evaluation k f E s)) :
    genericRank k f E s ≤ r - 1 := by
  have hle := genericRank_le k f E s
  have hne : genericRank k f E s ≠ r := fun h =>
    hn (evaluation_mono_of_genericRank_eq k f E s hreg hdim h)
  omega

/-- In particular, the nonmonic triple in the actual definition has
generic rank at most two. -/
theorem triple_genericRank_le_two_of_not_mono (E : X.Modules)
    (s : Fin 3 → cohomologyOverField k f E 0)
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)
    (hn : ¬ Mono (MukaiSemiIrreducible.evaluation k f E s)) : genericRank k f E s ≤ 2 :=
  genericRank_le_pred_of_not_mono k f E s hreg hdim hn

end M9Native.MukaiEvaluationGenericRank
