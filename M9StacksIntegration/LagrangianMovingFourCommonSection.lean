module

public import M9StacksIntegration.LagrangianCanonicalPointRanks
public import M9StacksIntegration.LagrangianTransverseGenusNine
public import M9StacksIntegration.PencilFibreVanishingMember
public import M9StacksIntegration.MukaiFourCircuit

/-! The original moving four-point fibre has one nonzero original six-
vector whose SAME original quotient section vanishes at all four points.
Every point factors through the SAME FULL native section-zero scheme.
The circuit's deletion independence and full span rank are derived from
the genuine native canonical restriction ranks. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
universe u

namespace M9Native.LagrangianMovingFourCommonSection
open LagrangianGrassmannian LagrangianUniversalSections LagrangianPrimitiveRestriction
open LagrangianPointKernelCoordinates LagrangianPointVolumeRanks
open LagrangianCanonicalPointRanks LagrangianOriginalSectionPoint

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]

/-- Honest native canonical restriction geometry supplies the actual
common vector and its actual original-section/full-zero-scheme meaning. -/
theorem exists_common_original_section_of_canonical_ranks
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsProper f] [IsCurve K f] [Smooth f]
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)]
    (l : X ⟶ space K)
    (c : restrictedLine K l ≅ Stacks.Duality.dualizingSheafOverField f)
    (hC : Function.Surjective (LagrangianPrimitiveRestriction.canonicalRestriction K f l c))
    (hl : l ≫ projection K = f)
    (p : Fin 4 → (Spec (.of K) ⟶ X)) (hp : ∀ i, p i ≫ f = 𝟙 _)
    (D : X.IdealSheafData)
    (hfac : ∀ i, ∃ a : Spec (.of K) ⟶ D.subscheme, a ≫ D.subschemeι = p i)
    (hrank : finrank K (LinearMap.range (CanonicalDivisorSpan.canonicalRestriction f D)) ≤ 3)
    (htriple : ∀ j : Fin 4, finrank K (LinearMap.range
      (CanonicalDivisorSpan.canonicalRestriction f (RationalPointDivisor.divisor
        (closedTuple K f (j.removeNth p) (fun i => hp (j.succAbove i)))))) = 3) :
    ∃ v : Fin 6 → K, v ≠ 0 ∧
      (∀ i, pullbackGlobalSections (p i) (bundle K l)
        ((cohomologyOverFieldZeroLinearIso K f (bundle K l)).hom (sectionMap K f l v)) = 0) ∧
      (∀ i, ∃ t : Spec (.of K) ⟶ (LagrangianHyperplaneEvaluation.zeroIdeal K f l v).subscheme,
        t ≫ (LagrangianHyperplaneEvaluation.zeroIdeal K f l v).subschemeι = p i) := by
  let w : Fin 4 → (⋀[K]^3 (Fin 6 → K)) := fun i => kernelVolume K (p i ≫ l)
  have hthree_rank (j : Fin 4) :
      finrank K (Submodule.span K (Set.range (j.removeNth w))) = 3 := by
    have h := kernelVolume_span_rank_eq_canonicalRestriction K f l c hC hl
      (j.removeNth p) (fun i => hp (j.succAbove i))
    rw [htriple j] at h
    exact h
  have hthree (j : Fin 4) : LinearIndependent K (j.removeNth w) := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    simpa only [Fintype.card_fin, Set.finrank] using (hthree_rank j).symm
  have hupper : finrank K (Submodule.span K (Set.range w)) ≤ 3 :=
    (kernelVolume_span_rank_le_full_divisor K f l c hC hl p hp D hfac).trans hrank
  have hsub : Submodule.span K (Set.range ((0 : Fin 4).removeNth w)) ≤
      Submodule.span K (Set.range w) := by
    apply Submodule.span_mono
    rintro _ ⟨i,rfl⟩
    exact ⟨(0 : Fin 4).succAbove i,rfl⟩
  have hlower := Submodule.finrank_mono hsub
  rw [hthree_rank 0] at hlower
  have hspan : finrank K (Submodule.span K (Set.range w)) = 3 := le_antisymm hupper hlower
  let u : Fin 4 → Fin 3 → (Fin 6 → K) := fun i => kernelRows K (p i ≫ l)
  obtain ⟨v,hv,hplanes⟩ := MukaiFourCircuit.exists_nonzero_mem_all_actual_planes K
    (two_ne_zero : (2 : K) ≠ 0) u (fun i => kernelRows_independent K (p i ≫ l)) hthree hspan
  refine ⟨v,hv,?_,?_⟩
  · intro i
    rw [sectionMap_constantVector]
    exact originalSection_point_zero_of_kernel_span K f l (p i) (hp i) v (hplanes i)
  · intro i
    exact factors_full_zero_of_kernel_span K f l (p i) (hp i) v (hplanes i)

/-- From an ORIGINAL degree-four pencil on the actual original LG cut,
the actual same-fibre points are all killed by one nonzero original
section. Genus, canonical completeness, member factors, triple ranks,
full-span rank and kernel frames are all derived. -/
theorem exists_original_pencil_fibre_common_section
    (M : Matrix (Fin 5) (Fin 14) K)
    [IsIntegral (LagrangianTransverseRestriction.curve K M)]
    [SmoothOfRelativeDimension 1 (LagrangianTransverseRestriction.curveProjection K M)]
    (hM : Function.Surjective M.mulVec)
    (hdim : topologicalKrullDim (LagrangianTransverseRestriction.curve K M) ≤ 1)
    (A : LinearSeries K (LagrangianTransverseRestriction.curveProjection K M) hdim 4 1) :
    ∃ D : PencilFourPointFibre.FourPointFibre K (LagrangianTransverseRestriction.curveProjection K M),
      ∃ v : Fin 6 → K, v ≠ 0 ∧
        (∀ i, pullbackGlobalSections (PencilFourPointFibre.curvePoint D i)
          (bundle K (LagrangianTransverseRestriction.inclusion K M))
          ((cohomologyOverFieldZeroLinearIso K (LagrangianTransverseRestriction.curveProjection K M)
            (bundle K (LagrangianTransverseRestriction.inclusion K M))).hom
              (sectionMap K (LagrangianTransverseRestriction.curveProjection K M)
                (LagrangianTransverseRestriction.inclusion K M) v)) = 0) ∧
        (∀ i, ∃ t : Spec (.of K) ⟶ (LagrangianHyperplaneEvaluation.zeroIdeal K
            (LagrangianTransverseRestriction.curveProjection K M)
            (LagrangianTransverseRestriction.inclusion K M) v).subscheme,
          t ≫ (LagrangianHyperplaneEvaluation.zeroIdeal K
            (LagrangianTransverseRestriction.curveProjection K M)
            (LagrangianTransverseRestriction.inclusion K M) v).subschemeι =
              PencilFourPointFibre.curvePoint D i) := by
  let f := LagrangianTransverseRestriction.curveProjection K M
  let l := LagrangianTransverseRestriction.inclusion K M
  let : Smooth f := SmoothOfRelativeDimension.smooth 1 _
  let : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop) :=
    isIso_globalSections_of_isAlgClosed K f
  obtain ⟨D,x,hx,hfac,hrank,htriple⟩ :=
    PencilFibreVanishingMember.exists_original_fibre_member_factors M hM hdim A
  let p := PencilFourPointFibre.curvePoint D
  have hp : ∀ i, p i ≫ f = 𝟙 _ := PencilFourPointFibre.curvePoint_overBase D
  have ht (j : Fin 4) : closedTuple K f (j.removeNth p)
      (fun i => hp (j.succAbove i)) = LagrangianPencilFibreTripleRank.triplePoints D j := by
    funext i
    rfl
  obtain ⟨v,hv,hzero,hJ⟩ := exists_common_original_section_of_canonical_ranks K f l
    (LagrangianTransverseCanonical.restrictedCanonicalIso K M hM)
    (LagrangianTransverseGenusNine.canonicalRestriction_surjective K M hM) rfl p hp
    (PencilMemberDivisor.divisor f hdim A x) hfac hrank (by intro j; rw [ht j]; exact htriple j)
  exact ⟨D,v,hv,hzero,hJ⟩

end M9Native.LagrangianMovingFourCommonSection
