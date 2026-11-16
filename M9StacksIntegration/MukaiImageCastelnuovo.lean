module

public import M9StacksIntegration.MukaiRankTwoSaturatedQuotient

/-!
# Castelnuovo applied to the actual image of global sections

For an original short exact sequence, the actual H0 image of its
quotient has dimension at least four when the middle H0 has dimension
six and the kernel H0 has dimension at most two. The genuine
four-section criterion on this actual image produces a saturated line
in the quotient, with two independent native sections whose original
images really lift to the middle sheaf. No lifting or line-selection
premise replaces that construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.MukaiImageCastelnuovo

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The original actual native H0 image, with its original inclusion. -/
def imageSections (S : ShortComplex X.Modules) :
    Submodule k (cohomologyOverField k f S.X₃ 0) :=
  LinearMap.range (cohomologyOverFieldMap k f S.g 0).hom

/-- Native H0 exactness computes this actual image dimension. -/
theorem finrank_imageSections_add
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [FiniteDimensional k (cohomologyOverField k f S.X₁ 0)]
    [FiniteDimensional k (cohomologyOverField k f S.X₂ 0)] :
    Module.finrank k (imageSections k f S) +
      Module.finrank k (cohomologyOverField k f S.X₁ 0) =
      Module.finrank k (cohomologyOverField k f S.X₂ 0) := by
  obtain ⟨δ,hinj,hex,hδ,hδ'⟩ := exists_cohomologyOverField_longExactSequence k f hS
  let u := (cohomologyOverFieldMap k f S.f 0).hom
  let v := (cohomologyOverFieldMap k f S.g 0).hom
  have hi : Function.Injective u := hinj
  have he : Function.Exact u v := hex 0
  have hdim := LinearMap.finrank_range_add_finrank_ker v
  rw [he.linearMap_ker_eq,LinearMap.finrank_range_of_inj hi] at hdim
  exact hdim

theorem four_le_finrank_imageSections
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [FiniteDimensional k (cohomologyOverField k f S.X₁ 0)]
    [FiniteDimensional k (cohomologyOverField k f S.X₂ 0)]
    (hE : Module.finrank k (cohomologyOverField k f S.X₂ 0) = 6)
    (hη : Module.finrank k (cohomologyOverField k f S.X₁ 0) ≤ 2) :
    4 ≤ Module.finrank k (imageSections k f S) := by
  have hdim := finrank_imageSections_add k f S hS
  omega

/-- The selected saturated line has actual independent original
sections whose images lie literally in the original H0 quotient image. -/
theorem exists_line_with_lifting_sections [IsAlgClosed k] [IsIntegral X]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} S.X₃ 2]
    [FiniteDimensional k (cohomologyOverField k f S.X₁ 0)]
    [FiniteDimensional k (cohomologyOverField k f S.X₂ 0)]
    [FiniteDimensional k (cohomologyOverField k f S.X₃ 0)]
    [FiniteDimensional k
      (cohomologyOverField k f (Scheme.Modules.exteriorPower S.X₃ 2) 0)]
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)
    (hE : Module.finrank k (cohomologyOverField k f S.X₂ 0) = 6)
    (hη : Module.finrank k (cohomologyOverField k f S.X₁ 0) ≤ 2)
    (hdet : Module.finrank k
      (cohomologyOverField k f (Scheme.Modules.exteriorPower S.X₃ 2) 0) ≤ 4) :
    ∃ (L N : X.Modules) (j : L ⟶ S.X₃) (q : S.X₃ ⟶ N) (w : j ≫ q = 0)
      (t : Fin 2 → cohomologyOverField k f L 0),
      SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L ∧
        SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N ∧
        (ShortComplex.mk j q w).ShortExact ∧
        LinearIndependent k t ∧
        ∀ a : Fin 2, cohomologyOverFieldMap k f j 0 (t a) ∈ imageSections k f S := by
  let G := S.X₃
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} G :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree G 2
  let : G.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree G
  let A := imageSections k f S
  have hA : 4 ≤ Module.finrank k A := four_le_finrank_imageSections k f S hS hE hη
  obtain ⟨a,b,hab,hw⟩ :=
    MukaiRankTwoCriterion.exists_two_sections_in_subspace_zero_exteriorEvaluation k f G A hA hdet
  let z : Fin 2 → cohomologyOverField k f G 0 := fun i => ((![a,b] i : A) : _)
  have hz : LinearIndependent k z := by
    convert hab.map' A.subtype (LinearMap.ker_eq_bot.mpr A.subtype_injective) using 1
    rfl
  have hzw : ExteriorEvaluation.lambda k f G 2 (exteriorPower.ιMulti k 2 z) = 0 := by
    convert hw using 1
    congr 1
  let φ := MukaiSemiIrreducible.evaluation k f G z
  let : (cokernel φ).IsQuasicoherent :=
    MukaiSaturationSections.evaluation_cokernel_isQuasicoherent k f G z
  let L := MukaiEvaluationSaturation.saturation φ
  let N := MukaiEvaluationSaturation.torsionFreeQuotient φ
  let j := MukaiEvaluationSaturation.inclusion φ
  let q := MukaiEvaluationSaturation.projection φ
  let t : Fin 2 → cohomologyOverField k f L 0 := fun i =>
    MukaiSaturationSections.liftedSectionH0 k f φ
      (_root_.SheafOfModules.freeSection (ULift.up i))
  have ht (i : Fin 2) : cohomologyOverFieldMap k f j 0 (t i) = z i := by
    exact (MukaiSaturationSections.cohomologyMap_liftedSectionH0 k f φ _).trans
      (MukaiSaturationSections.imageSectionH0_evaluation k f G z i)
  obtain ⟨hL,hN,hseq,h0⟩ :=
    MukaiRankTwoSaturatedQuotient.pair_line_quotient k f G z hreg hdim hz hzw
  refine ⟨L,N,j,q,kernel.condition _,t,hL,hN,hseq,?_,?_⟩
  · apply LinearIndependent.of_comp (cohomologyOverFieldMap k f j 0).hom
    convert hz using 1
    funext i
    exact ht i
  · intro i
    rw [ht]
    exact (![a,b] i : A).property

end M9Native.MukaiImageCastelnuovo
