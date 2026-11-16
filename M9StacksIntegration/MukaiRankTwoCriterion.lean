module

public import M9StacksIntegration.ExteriorEvaluation
public import M9StacksIntegration.MukaiCastelnuovoLinear

/-!
# The native rank-two determinant-wedge criterion

Mukai Proposition 3.2, in the four-section rank-two case used in
Proposition 5.3, is applied here to the actual native exterior evaluation
map. No alternating evaluation or decomposable kernel vector is assumed:
the former is constructed from the actual sheaf exterior algebra and the
latter is produced by the proved Plücker argument.

The conclusion is vanishing of the wedge of two independent genuine
sections. Turning its generated rank-one subsheaf into a saturated line
subbundle retaining these sections is a separate sheaf-theoretic step.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.MukaiRankTwoCriterion

variable (k : Type u) [Field k] [IsAlgClosed k]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (F : X.Modules)

/-- Four sections and at most four sections of the second exterior power
give an independent pair with zero actual determinant evaluation. When
`F` has rank two, its second exterior power is its top exterior line. -/
theorem exists_two_sections_zero_exteriorEvaluation
    [FiniteDimensional k (cohomologyOverField k f F 0)]
    [FiniteDimensional k
      (cohomologyOverField k f (Scheme.Modules.exteriorPower F 2) 0)]
    (hsections : 4 ≤ Module.finrank k (cohomologyOverField k f F 0))
    (hdet : Module.finrank k
      (cohomologyOverField k f (Scheme.Modules.exteriorPower F 2) 0) ≤ 4) :
    ∃ a b : cohomologyOverField k f F 0,
      LinearIndependent k ![a,b] ∧
        ExteriorEvaluation.lambda k f F 2 (exteriorPower.ιMulti k 2 ![a,b]) = 0 := by
  let B := (ExteriorEvaluation.lambda k f F 2).compAlternatingMap
    (exteriorPower.ιMulti k 2)
  obtain ⟨a,b,hab,hzero⟩ :=
    MukaiCastelnuovoLinear.exists_independent_pair_zero_of_finrank B hsections hdet
  exact ⟨a,b,hab,hzero⟩

/-- The same criterion for an actual finite-dimensional section
subspace, with the original inclusion in native sheaf cohomology. -/
theorem exists_two_sections_in_subspace_zero_exteriorEvaluation
    (A : Submodule k (cohomologyOverField k f F 0)) [FiniteDimensional k A]
    [FiniteDimensional k
      (cohomologyOverField k f (Scheme.Modules.exteriorPower F 2) 0)]
    (hsections : 4 ≤ Module.finrank k A)
    (hdet : Module.finrank k
      (cohomologyOverField k f (Scheme.Modules.exteriorPower F 2) 0) ≤ 4) :
    ∃ a b : A, LinearIndependent k ![a,b] ∧
      ExteriorEvaluation.lambda k f F 2
        (exteriorPower.ιMulti k 2 ![(a : cohomologyOverField k f F 0),
          (b : cohomologyOverField k f F 0)]) = 0 := by
  let B := ((ExteriorEvaluation.lambda k f F 2).compAlternatingMap
    (exteriorPower.ιMulti k 2)).compLinearMap A.subtype
  obtain ⟨a,b,hab,hzero⟩ :=
    MukaiCastelnuovoLinear.exists_independent_pair_zero_of_finrank B hsections hdet
  refine ⟨a,b,hab,?_⟩
  change ExteriorEvaluation.lambda k f F 2
    (exteriorPower.ιMulti k 2 (fun i => ((![a,b] i : A) :
      cohomologyOverField k f F 0))) = 0 at hzero
  convert hzero using 1
  congr 2

end M9Native.MukaiRankTwoCriterion
