module

public import M9StacksIntegration.MukaiRankTwoSaturatedLine

/-!
# The actual line quotient of a saturated zero-wedge pair

The quotient is the original torsion-free quotient of the original
evaluation cokernel. Its local freeness is already obtained from
torsion freeness on the regular curve. Additivity of genuine generic
stalk ranks in the original saturation short exact sequence derives
its rank one from rank two of the given bundle and rank one of the
constructed saturation. Thus both terms are actual line bundles, and
the original kernel/projection maps form the required short exact
sequence.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.MukaiRankTwoSaturatedQuotient

section Pair

open MukaiEvaluationSaturation

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
variable (f : X ⟶ Spec (.of k)) (F : X.Modules) [F.IsQuasicoherent]
variable [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
variable (s : Fin 2 → cohomologyOverField k f F 0)
variable [(cokernel (MukaiSemiIrreducible.evaluation k f F s)).IsQuasicoherent]

/-- The original quotient has rank one; this rank is derived by exact
generic-stalk additivity and is not an input. -/
theorem pair_quotient_rank_one
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)
    (hs : LinearIndependent k s)
    (hw : ExteriorEvaluation.lambda k f F 2 (exteriorPower.ιMulti k 2 s) = 0) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (torsionFreeQuotient (MukaiSemiIrreducible.evaluation k f F s)) 1 := by
  let φ := MukaiSemiIrreducible.evaluation k f F s
  let hF : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F 2
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  let : F.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X F
  let : (saturation φ).IsCoherent := saturation_isCoherent φ
  let : (torsionFreeQuotient φ).IsCoherent := torsionFreeQuotient_isCoherent φ
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (saturation φ) 1 :=
    MukaiSaturationRank.evaluation_saturation_rank_one k f F s hreg hdim hF (hs.ne_zero 0) hw
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (torsionFreeQuotient φ) :=
    torsionFreeQuotient_isFiniteLocallyFree φ hreg hdim hF
  have hadd := Scheme.Modules.fiberRank_genericPoint_add_of_shortExact
    (ShortComplex.mk (inclusion φ) (projection φ) (kernel.condition (projection φ)))
    (sequence_shortExact φ)
  have hFtwo := Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank F 2 (genericPoint X)
  have hLone := Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank
    (saturation φ) 1 (genericPoint X)
  have hQone : Scheme.Modules.fiberRank (torsionFreeQuotient φ) (genericPoint X) = 1 := by
    change Scheme.Modules.fiberRank F (genericPoint X) =
      Scheme.Modules.fiberRank (saturation φ) (genericPoint X) +
        Scheme.Modules.fiberRank (torsionFreeQuotient φ) (genericPoint X) at hadd
    rw [hFtwo,hLone] at hadd
    omega
  exact Scheme.Modules.isFiniteLocallyFreeOfRank_of_fiberRank_eq
    (torsionFreeQuotient φ) 1 (genericPoint X) hQone

/-- The very torsion-free quotient used to construct the saturation
is invertible. -/
theorem pair_quotient_invertible
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)
    (hs : LinearIndependent k s)
    (hw : ExteriorEvaluation.lambda k f F 2 (exteriorPower.ιMulti k 2 s) = 0) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (torsionFreeQuotient (MukaiSemiIrreducible.evaluation k f F s)) := by
  let := pair_quotient_rank_one k f F s hreg hdim hs hw
  exact Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace _

/-- Both original constructed terms are line bundles, and their
original kernel/projection maps form the actual short exact sequence. -/
theorem pair_line_quotient
    [FiniteDimensional k (cohomologyOverField k f F 0)]
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)
    (hs : LinearIndependent k s)
    (hw : ExteriorEvaluation.lambda k f F 2 (exteriorPower.ιMulti k 2 s) = 0) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (saturation (MukaiSemiIrreducible.evaluation k f F s)) ∧
      SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        (torsionFreeQuotient (MukaiSemiIrreducible.evaluation k f F s)) ∧
      (ShortComplex.mk
        (inclusion (MukaiSemiIrreducible.evaluation k f F s))
        (projection (MukaiSemiIrreducible.evaluation k f F s))
        (kernel.condition (projection (MukaiSemiIrreducible.evaluation k f F s)))).ShortExact ∧
      2 ≤ Module.finrank k (cohomologyOverField k f
        (saturation (MukaiSemiIrreducible.evaluation k f F s)) 0) := by
  let hF : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F 2
  exact ⟨MukaiSaturationRank.evaluation_saturation_invertible k f F s hreg hdim hF
      (hs.ne_zero 0) hw,
    pair_quotient_invertible k f F s hreg hdim hs hw,
    sequence_shortExact _,
    MukaiSaturationSections.evaluation_saturation_h0_lower_bound k f F s hs⟩

end Pair

section FourSections

variable (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} [IsIntegral X]
variable (f : X ⟶ Spec (.of k)) (F : X.Modules)
variable [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
variable [FiniteDimensional k (cohomologyOverField k f F 0)]
variable [FiniteDimensional k
  (cohomologyOverField k f (Scheme.Modules.exteriorPower F 2) 0)]

/-- The four-section criterion yields actual line bundles and actual
original short exact maps, with no quotient-rank or line premise. -/
theorem exists_saturated_line_quotient
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)
    (hsections : 4 ≤ Module.finrank k (cohomologyOverField k f F 0))
    (hdet : Module.finrank k
      (cohomologyOverField k f (Scheme.Modules.exteriorPower F 2) 0) ≤ 4) :
    ∃ (L N : X.Modules) (j : L ⟶ F) (q : F ⟶ N) (w : j ≫ q = 0),
      SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L ∧
        SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N ∧
        (ShortComplex.mk j q w).ShortExact ∧
        2 ≤ Module.finrank k (cohomologyOverField k f L 0) := by
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F 2
  let : F.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree F
  obtain ⟨a,b,hab,hw⟩ :=
    MukaiRankTwoCriterion.exists_two_sections_zero_exteriorEvaluation k f F hsections hdet
  let s := ![a,b]
  let φ := MukaiSemiIrreducible.evaluation k f F s
  let : (cokernel φ).IsQuasicoherent :=
    MukaiSaturationSections.evaluation_cokernel_isQuasicoherent k f F s
  exact ⟨MukaiEvaluationSaturation.saturation φ,MukaiEvaluationSaturation.torsionFreeQuotient φ,
    MukaiEvaluationSaturation.inclusion φ,MukaiEvaluationSaturation.projection φ,
    kernel.condition _,pair_line_quotient k f F s hreg hdim hab hw⟩

end FourSections

end M9Native.MukaiRankTwoSaturatedQuotient
