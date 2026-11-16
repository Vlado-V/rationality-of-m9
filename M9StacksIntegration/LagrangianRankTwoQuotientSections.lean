module

public import M9StacksIntegration.LagrangianRankTwoSubsystemExistence
public import M9StacksIntegration.LagrangianOriginalSubsystemSemi
public import M9StacksIntegration.LagrangianPrimitiveRestrictionInjection
public import M9StacksIntegration.MukaiBundleRecognition
public import M9StacksIntegration.MukaiRecognitionHomBound

/-! The image of the original six-section system in its actual
rank-one quotient has dimension exactly three. Semi3 is used only on
the original section subspace; completeness of H0(E) or H0(alpha) is
never assumed. In particular this does not identify all of H0(alpha),
and does not yet prove the pentagonal contradiction. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module TopologicalSpace
universe u

namespace M9Native.LagrangianRankTwoQuotientSections

section Semi

variable (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}}
  [IsIntegral X] (f : X ⟶ Spec (.of K)) [IsProper f]
  (E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]

/-- The four-section exclusion holds inside the actual Semi3 section
subspace, with no complete-system hypothesis. -/
theorem four_rank_exclusion_of_semi
    (A : Submodule K (cohomologyOverField K f E 0))
    (hsemi : MukaiSemiIrreducible.SemiIrreducible K f E 3 A)
    (s : Fin 4 → cohomologyOverField K f E 0) (hs : LinearIndependent K s)
    (hsA : ∀ i, s i ∈ A) :
    ∃ x : X, 3 ≤ MukaiSemiIrreducible.mapRankAt
      (MukaiSemiIrreducible.evaluation K f E s) x := by
  classical
  let : Module.Finite K (cohomologyOverField K f E 0) :=
    MukaiRecognitionHomBound.finite_bundle_H0 K f E 3
  by_contra hn
  have hbad (y : X) : MukaiSemiIrreducible.mapRankAt
      (MukaiSemiIrreducible.evaluation K f E s) y ≤ 2 := by
    have hnot : ¬3 ≤ MukaiSemiIrreducible.mapRankAt
        (MukaiSemiIrreducible.evaluation K f E s) y := fun h => hn ⟨y, h⟩
    omega
  obtain ⟨p, hp⟩ := BaseFieldPoints.exists_point f
  let c := pointEquivClosedPoint f ⟨p, hp⟩
  let x := c.val
  have hx : IsClosed ({x} : Set X) := c.property
  let e := MukaiSemiExclusions.closedEvaluation K f E x hx
  have hbadpoint : finrank K (MukaiSemiExclusions.valueSpan e s) ≤ 2 := by
    simpa only [MukaiSemiExclusions.closedEvaluation_rank K f E x hx] using hbad x
  obtain ⟨t, ht, hin, hsmall⟩ := MukaiSemiExclusions.exists_triple_in_four e s hs hbadpoint
  have hpoint : MukaiSemiIrreducible.mapRankAt
      (MukaiSemiIrreducible.evaluation K f E t) x ≤ 1 := by
    rw [MukaiSemiExclusions.closedEvaluation_rank K f E x hx]
    exact hsmall
  let y := genericPoint X
  let := TupleEvaluationFiber.fiberFinite E 3 y
  have hgeneric : MukaiSemiIrreducible.mapRankAt
      (MukaiSemiIrreducible.evaluation K f E t) y ≤ 2 := by
    rw [MukaiSemiExclusions.mapRankAt_eq_finrank_valueSpan]
    have hle := Submodule.finrank_mono
      (MukaiSemiExclusions.valueSpan_mono (TupleEvaluationFiber.sectionValue K f E y) s t hin)
    have hb := hbad y
    rw [MukaiSemiExclusions.mapRankAt_eq_finrank_valueSpan] at hb
    exact hle.trans hb
  have htA (i : Fin 3) : t i ∈ A := by
    exact (Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hsA j)) (hin i)
  let tA : Fin 3 → A := fun i => ⟨t i, htA i⟩
  have htAli : LinearIndependent K tA :=
    LinearIndependent.of_comp A.subtype ht
  rcases hsemi tA htAli with hm | hr
  · change Mono (MukaiSemiIrreducible.evaluation K f E t) at hm
    let := hm
    have h := MukaiSemiExclusions.mapRankAt_generic_of_mono K f E t
    change MukaiSemiIrreducible.mapRankAt
      (MukaiSemiIrreducible.evaluation K f E t) y = 3 at h
    omega
  · have h := hr x
    change MukaiSemiIrreducible.mapRankAt
      (MukaiSemiIrreducible.evaluation K f E t) x = 2 at h
    omega

/-- In any genuine rank-two quotient sequence, at most three of an
injective original Semi3 system can lie in the actual H0 kernel. The
kernel and its dimension are conclusions, not linear-system inputs. -/
theorem kernel_composite_finrank_le_three
    {V : Type u} [AddCommGroup V] [Module K V] [Module.Finite K V]
    (a : V →ₗ[K] cohomologyOverField K f E 0) (ha : Function.Injective a)
    (hsemi : MukaiSemiIrreducible.SemiIrreducible K f E 3 (LinearMap.range a))
    (F L : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
    (j : F ⟶ E) (q : E ⟶ L) (w : j ≫ q = 0)
    (hS : (ShortComplex.mk j q w).ShortExact) :
    finrank K (LinearMap.ker ((cohomologyOverFieldMap K f q 0).hom.comp a)) ≤ 3 := by
  classical
  by_contra hn
  let theta := (cohomologyOverFieldMap K f q 0).hom.comp a
  change ¬ finrank K (LinearMap.ker theta) ≤ 3 at hn
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank
    (by omega : 4 ≤ finrank K (LinearMap.ker theta))
  let s : Fin 4 → cohomologyOverField K f E 0 := fun i => a (v i).val
  have hs : LinearIndependent K s :=
    (hv.map' theta.ker.subtype (Submodule.ker_subtype _)).map' a (LinearMap.ker_eq_bot.mpr ha)
  obtain ⟨x, hx⟩ := four_rank_exclusion_of_semi K f E (LinearMap.range a) hsemi s hs
    (fun i => ⟨(v i).val, rfl⟩)
  obtain ⟨_, _, he, _, _⟩ := exists_cohomologyOverField_longExactSequence K f hS
  have hlift (i : Fin 4) : ∃ z : cohomologyOverField K f F 0,
      cohomologyOverFieldMap K f j 0 z = s i := by
    have hmem : s i ∈ LinearMap.ker (cohomologyOverFieldMap K f q 0).hom := (v i).property
    rw [(he 0).linearMap_ker_eq] at hmem
    exact hmem
  choose z hz using hlift
  have hzt : (fun i : Fin 4 => cohomologyOverFieldMap K f j 0 (z i)) = s := funext hz
  have hb := MukaiBundleRecognition.mapRankAt_factor_le
    (MukaiSemiIrreducible.evaluation K f F z) j 2 x
  rw [MukaiEvaluationChoices.evaluation_postcomp, hzt] at hb
  omega

end Semi

section ActualModel

open LagrangianOrderedFibre LagrangianUniversalSections
open LagrangianRankTwoSubsystemBundles LagrangianRankTwoSubsystemExistence

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)

/-- The literal original six-section map followed by the actual
categorical quotient to alpha, using the original field cohomology. -/
def alphaSections (s : Fin 3 → (Fin 6 → K)) :
    (Fin 6 → K) →ₗ[K] cohomologyOverField K (modelProjection K M hM) (alpha K M hM s) 0 :=
  (cohomologyOverFieldMap K (modelProjection K M hM) (cokernel.π (originalMap K M hM s)) 0).hom.comp
    (sectionMap K (modelProjection K M hM) (modelInclusion K M hM))

variable [IsIntegral (model K M hM)]
  [SmoothOfRelativeDimension 1 (modelProjection K M hM)]

/-- The actual Semi3 geometry bounds the original quotient kernel
without identifying the six original sections with complete H0(E). -/
theorem alphaSections_kernel_le_three (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) :
    finrank K (LinearMap.ker (alphaSections K M hM s)) ≤ 3 := by
  let : IsProper (modelProjection K M hM) := model_proper K M hM
  let := bundle_rank K (modelInclusion K M hM)
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (imageBundle K M hM s) 2 :=
    (ranks K M hM s hr).2.1
  have ha : Function.Injective
      (sectionMap K (modelProjection K M hM) (modelInclusion K M hM)) := by
    apply LagrangianPrimitiveRestrictionInjection.universal_sectionMap_injective_of_restriction_rank
      K (modelProjection K M hM) (modelInclusion K M hM) rfl
    rw [LagrangianModelRestriction.primitiveRestriction_range_finrank K M hM]
    norm_num
  exact kernel_composite_finrank_le_three K (modelProjection K M hM)
    (bundle K (modelInclusion K M hM))
    (sectionMap K (modelProjection K M hM) (modelInclusion K M hM)) ha
    (LagrangianOriginalSubsystemSemi.originalSubsystem_semi K M hM)
    (imageBundle K M hM s) (alpha K M hM s)
    (image.ι (originalMap K M hM s)) (cokernel.π (originalMap K M hM s))
    (quotientSequence K M hM s).zero (quotientSequence_shortExact K M hM s)

/-- The true independent original rank-two net supplies the other
inequality, so the actual six-section quotient kernel has dimension three. -/
theorem alphaSections_kernel_finrank (s : Fin 3 → (Fin 6 → K)) (hs : LinearIndependent K s)
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) :
    finrank K (LinearMap.ker (alphaSections K M hM s)) = 3 := by
  let : IsProper (modelProjection K M hM) := model_proper K M hM
  obtain ⟨_, _, he, _, _⟩ := exists_cohomologyOverField_longExactSequence K
    (modelProjection K M hM) (quotientSequence_shortExact K M hM s)
  have hex : Function.Exact
      (cohomologyOverFieldMap K (modelProjection K M hM)
        (image.ι (originalMap K M hM s)) 0).hom
      (cohomologyOverFieldMap K (modelProjection K M hM)
        (cokernel.π (originalMap K M hM s)) 0).hom := he 0
  have hmem (i : Fin 3) : s i ∈ LinearMap.ker (alphaSections K M hM s) := by
    change sectionMap K (modelProjection K M hM) (modelInclusion K M hM) (s i) ∈
      LinearMap.ker (cohomologyOverFieldMap K (modelProjection K M hM)
        (cokernel.π (originalMap K M hM s)) 0).hom
    rw [hex.linearMap_ker_eq]
    exact ⟨imageSections K M hM s i, imageSections_maps_to_original K M hM s i⟩
  let t : Fin 3 → LinearMap.ker (alphaSections K M hM s) := fun i => ⟨s i, hmem i⟩
  have ht : LinearIndependent K t :=
    LinearIndependent.of_comp (alphaSections K M hM s).ker.subtype hs
  have hlow : 3 ≤ finrank K (LinearMap.ker (alphaSections K M hM s)) := by
    simpa only [Fintype.card_fin] using ht.fintype_card_le_finrank
  exact (alphaSections_kernel_le_three K M hM s hr).antisymm hlow

/-- The original image W in H0(alpha) is a genuine three-dimensional
subsystem. Completeness of H0(alpha) is not part of this conclusion. -/
theorem alphaSections_range_finrank (s : Fin 3 → (Fin 6 → K)) (hs : LinearIndependent K s)
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) :
    finrank K (LinearMap.range (alphaSections K M hM s)) = 3 := by
  have h := (alphaSections K M hM s).finrank_range_add_finrank_ker
  rw [alphaSections_kernel_finrank K M hM s hs hr] at h
  have h6 : finrank K (Fin 6 → K) = 6 := by simp
  omega

end ActualModel

end M9Native.LagrangianRankTwoQuotientSections
