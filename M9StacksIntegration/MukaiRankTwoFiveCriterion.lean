module

public import M9StacksIntegration.MukaiCastelnuovoFive
public import M9StacksIntegration.MukaiSaturationRank
public import M9StacksIntegration.MukaiRankTwoSaturatedQuotient

/-!
# The actual five-section rank-two determinant-wedge criterion

This is the five-section case of Mukai Proposition 3.2 needed in
Lemma 5.4. The actual native exterior evaluation has a decomposable
kernel vector by genuine Grassmannian projective intersection. On a
regular integral curve, its prescribed evaluation saturation is an
invertible subsheaf retaining two independent original sections.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.MukaiRankTwoFiveCriterion

variable (k : Type u) [Field k] [IsAlgClosed k]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (F : X.Modules)
variable [FiniteDimensional k (cohomologyOverField k f F 0)]
variable [FiniteDimensional k
  (cohomologyOverField k f (Scheme.Modules.exteriorPower F 2) 0)]

/-- Five sections and at most five sections of the actual second
exterior power give an independent pair with zero determinant evaluation. -/
theorem exists_two_sections_zero_exteriorEvaluation
    (hsections : 5 ≤ Module.finrank k (cohomologyOverField k f F 0))
    (hdet : Module.finrank k
      (cohomologyOverField k f (Scheme.Modules.exteriorPower F 2) 0) ≤ 5) :
    ∃ a b : cohomologyOverField k f F 0,
      LinearIndependent k ![a,b] ∧
        ExteriorEvaluation.lambda k f F 2 (exteriorPower.ιMulti k 2 ![a,b]) = 0 := by
  let B := (ExteriorEvaluation.lambda k f F 2).compAlternatingMap
    (exteriorPower.ιMulti k 2)
  obtain ⟨a,b,hab,hzero⟩ :=
    MukaiCastelnuovoFive.exists_independent_pair_zero_of_finrank k B hsections hdet
  exact ⟨a,b,hab,hzero⟩

/-- The line in the five-section criterion is constructed from the
original pair's evaluation image, and retains at least two sections. -/
theorem exists_pair_with_saturated_line [IsIntegral X]
    [SheafOfModules.IsFiniteLocallyFree.{u,u,u} F]
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)
    (hsections : 5 ≤ Module.finrank k (cohomologyOverField k f F 0))
    (hdet : Module.finrank k
      (cohomologyOverField k f (Scheme.Modules.exteriorPower F 2) 0) ≤ 5) :
    ∃ s : Fin 2 → cohomologyOverField k f F 0,
      LinearIndependent k s ∧
        ExteriorEvaluation.lambda k f F 2 (exteriorPower.ιMulti k 2 s) = 0 ∧
          (letI : F.IsQuasicoherent :=
            Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree F
           letI : (cokernel (MukaiSemiIrreducible.evaluation k f F s)).IsQuasicoherent :=
            MukaiSaturationSections.evaluation_cokernel_isQuasicoherent k f F s
           SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
               (MukaiEvaluationSaturation.saturation
                 (MukaiSemiIrreducible.evaluation k f F s)) ∧
             2 ≤ Module.finrank k (cohomologyOverField k f
               (MukaiEvaluationSaturation.saturation
                 (MukaiSemiIrreducible.evaluation k f F s)) 0)) := by
  obtain ⟨a,b,hab,hw⟩ :=
    exists_two_sections_zero_exteriorEvaluation k f F hsections hdet
  exact ⟨![a,b],hab,hw,
    MukaiSaturationRank.actual_pair_saturation_line_with_two_sections
      k f F ![a,b] hreg hdim hab hw⟩

/-- The five-section criterion produces the two actual line bundles
with the actual original saturation short exact maps. -/
theorem exists_saturated_line_quotient [IsIntegral X]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)
    (hsections : 5 ≤ Module.finrank k (cohomologyOverField k f F 0))
    (hdet : Module.finrank k
      (cohomologyOverField k f (Scheme.Modules.exteriorPower F 2) 0) ≤ 5) :
    ∃ (L N : X.Modules) (j : L ⟶ F) (q : F ⟶ N) (w : j ≫ q = 0),
      SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L ∧
        SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N ∧
        (ShortComplex.mk j q w).ShortExact ∧
        2 ≤ Module.finrank k (cohomologyOverField k f L 0) := by
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F 2
  let : F.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree F
  obtain ⟨a,b,hab,hw⟩ := exists_two_sections_zero_exteriorEvaluation k f F hsections hdet
  let s := ![a,b]
  let φ := MukaiSemiIrreducible.evaluation k f F s
  let : (cokernel φ).IsQuasicoherent :=
    MukaiSaturationSections.evaluation_cokernel_isQuasicoherent k f F s
  exact ⟨MukaiEvaluationSaturation.saturation φ,MukaiEvaluationSaturation.torsionFreeQuotient φ,
    MukaiEvaluationSaturation.inclusion φ,MukaiEvaluationSaturation.projection φ,
    kernel.condition _,MukaiRankTwoSaturatedQuotient.pair_line_quotient k f F s hreg hdim hab hw⟩

end M9Native.MukaiRankTwoFiveCriterion
