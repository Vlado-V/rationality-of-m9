module

public import M9StacksIntegration.MukaiRecognitionHomBound
public import M9StacksIntegration.MukaiSemiExclusions
public import M9StacksIntegration.MukaiEvaluationImage
public import M9StacksIntegration.MukaiGeneratedQuotient
public import M9StacksIntegration.MukaiCompleteDualSpanSections
public import M9StacksIntegration.CompleteEvaluationGeneration
public import M9StacksIntegration.MukaiThreeSectionDeterminant
public import M9StacksIntegration.MukaiNoDegreeSevenNet
public import M9StacksIntegration.MukaiShortExactFiberRank
public import Mathlib.RingTheory.LocalRing.Module
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRankGeneral
public import M9StacksIntegration.MukaiDualSpanDeterminant
public import M9StacksIntegration.MukaiThreeGeneratorRecognition
public import M9StacksIntegration.MukaiCompleteEvaluation

/-!
# Recognition of the actual Mukai rank-three bundle

The recognition argument retains the original sheaf morphisms produced
by the actual Hom alternative. Generic ranks, categorical images and
semi-irreducibility exclusions are used to prove properties of those
maps, rather than adding monicity, epimorphy or an image classification
as inputs. The accompanying receipt distinguishes checked intermediate
branches from the full extension-recognition endpoint.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct
open Stacks.AlgebraicGeometry.ReflexiveModules
open M9Native.MukaiBundle M9Native.MukaiBundleDeterminant

universe u

namespace M9Native.MukaiBundleRecognition

variable {X : Scheme.{u}}

/-- Cancel an actual invertible right tensor factor, using the actual
native tensor equivalence on sheaves of modules. -/
def tensorCancelRightIso (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    {A B : X.Modules} (e : tensor A L ≅ tensor B L) : A ≅ B := by
  let F := M9StacksIntegration.InvertibleHomCancellation.tensorRight L
  letI : F.IsEquivalence := Scheme.Modules.isEquivalence_invertibleTensorRightFunctor L
  letI : F.Faithful := Functor.IsEquivalence.faithful
  letI : F.Full := Functor.IsEquivalence.full
  exact F.preimageIso e

/-- Composition on the actual residue-field fibres. -/
theorem fiberMap_comp {A B C : X.Modules} (a : A ⟶ B) (b : B ⟶ C) (x : X) :
    MukaiSemiIrreducible.fiberMap (a ≫ b) x =
      (MukaiSemiIrreducible.fiberMap b x).comp (MukaiSemiIrreducible.fiberMap a x) := by
  letI := TupleEvaluationFiber.residueAlgebra x
  letI := Stacks.SheafOfModules.FlatShortExact.stalkModule (X := X.toRingedSpace) A x
  letI := Stacks.SheafOfModules.FlatShortExact.stalkModule (X := X.toRingedSpace) B x
  letI := Stacks.SheafOfModules.FlatShortExact.stalkModule (X := X.toRingedSpace) C x
  have h : MukaiSaturationRank.stalkMap (a ≫ b) x =
      (MukaiSaturationRank.stalkMap b x).comp (MukaiSaturationRank.stalkMap a x) := by
    ext m
    exact MukaiSaturationRank.stalkMap_comp a b x m
  change (MukaiSaturationRank.stalkMap (a ≫ b) x).baseChange (X.residueField x) =
    (MukaiSaturationRank.stalkMap b x).baseChange (X.residueField x) ∘ₗ
      (MukaiSaturationRank.stalkMap a x).baseChange (X.residueField x)
  rw [h, LinearMap.baseChange_comp]

/-- Factoring through an actual rank-r bundle bounds the original
map's actual fibre rank by r at every point. -/
theorem mapRankAt_factor_le {A B C : X.Modules} (a : A ⟶ B) (b : B ⟶ C)
    (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} B r] (x : X) :
    MukaiSemiIrreducible.mapRankAt (a ≫ b) x ≤ r := by
  letI := TupleEvaluationFiber.residueAlgebra x
  letI := TupleEvaluationFiber.fiberFinite B r x
  change Module.finrank (X.residueField x)
    (LinearMap.range (MukaiSemiIrreducible.fiberMap (a ≫ b) x)) ≤ r
  rw [fiberMap_comp, LinearMap.range_comp]
  exact (Submodule.finrank_map_le _ _).trans
    ((Submodule.finrank_le _).trans_eq (TupleEvaluationFiber.finrank_fiber B r x))

/-- The original residue-fibre maps detect epimorphy onto an actual
coherent sheaf. The converse is local Nakayama on the actual stalk map,
using the genuine residue-field quotient, not a fibre-epimorphy premise
for the sheaf itself. -/
theorem epi_of_fiberMap_surjective {A B : X.Modules} [B.IsCoherent]
    (a : A ⟶ B) (ha : ∀ x : X, Function.Surjective (MukaiSemiIrreducible.fiberMap a x)) :
    Epi a := by
  apply (AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap
    (O := X.ringCatSheaf) a).mpr
  intro x
  letI := TupleEvaluationFiber.residueAlgebra x
  letI := Stacks.SheafOfModules.FlatShortExact.stalkModule (X := X.toRingedSpace) A x
  letI := Stacks.SheafOfModules.FlatShortExact.stalkModule (X := X.toRingedSpace) B x
  letI : Module.Finite (X.presheaf.stalk x) (MukaiSaturationRank.Stalk B x) :=
    Scheme.Modules.finite_stalk_of_isCoherent B x
  let q : MukaiSaturationRank.Stalk B x →ₗ[X.presheaf.stalk x]
      (X.residueField x ⊗[X.presheaf.stalk x] MukaiSaturationRank.Stalk B x) :=
    TensorProduct.mk (X.presheaf.stalk x) (X.residueField x) (MukaiSaturationRank.Stalk B x) 1
  have hcomp : Function.Surjective (q.comp (MukaiSaturationRank.stalkMap a x)) := by
    intro t
    obtain ⟨z, hz⟩ := ha x t
    obtain ⟨m, hm⟩ := TensorProduct.mk_surjective (X.presheaf.stalk x)
      (MukaiSaturationRank.Stalk A x) (X.residueField x) Ideal.Quotient.mk_surjective z
    refine ⟨m, ?_⟩
    change (1 : X.residueField x) ⊗ₜ[X.presheaf.stalk x]
      (MukaiSaturationRank.stalkMap a x m) = t
    calc
      _ = MukaiSemiIrreducible.fiberMap a x
          ((1 : X.residueField x) ⊗ₜ[X.presheaf.stalk x] m) :=
        (LinearMap.baseChange_tmul _ _ _).symm
      _ = t := (congrArg (MukaiSemiIrreducible.fiberMap a x) hm).trans hz
  have hmap : (LinearMap.range (MukaiSaturationRank.stalkMap a x)).map q = ⊤ := by
    rw [← LinearMap.range_comp]
    exact LinearMap.range_eq_top.mpr hcomp
  have hrange : LinearMap.range (MukaiSaturationRank.stalkMap a x) = ⊤ :=
    (IsLocalRing.map_tensorProduct_mk_eq_top
      (R := X.presheaf.stalk x) (M := MukaiSaturationRank.Stalk B x)).mp hmap
  intro y
  obtain ⟨m, hm⟩ := LinearMap.range_eq_top.mp hrange y
  exact ⟨m, (MukaiSaturationRank.stalkMap_native a x m).symm.trans hm⟩

/-- The actual cokernel is locally free when the actual map between
bundles is injective on every residue fibre. Local free cokernels follow
from the native local-ring tensor-injectivity criterion, then the native
stalk characterization of finite local freeness. -/
theorem cokernel_finiteLocallyFree_of_fiberMap_injective [IsLocallyNoetherian X]
    {Q E : X.Modules}
    [SheafOfModules.IsFiniteLocallyFree.{u,u,u} Q]
    [SheafOfModules.IsFiniteLocallyFree.{u,u,u} E]
    (a : Q ⟶ E) (ha : ∀ x : X, Function.Injective (MukaiSemiIrreducible.fiberMap a x)) :
    SheafOfModules.IsFiniteLocallyFree.{u,u,u} (cokernel a) := by
  letI : Q.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X Q
  letI : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X E
  letI : Q.IsQuasicoherent := isQuasicoherent_of_isCoherent Q
  letI : E.IsQuasicoherent := isQuasicoherent_of_isCoherent E
  letI : (cokernel a).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel a
  letI : (cokernel a).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_of_epi_of_isQuasicoherent (cokernel.π a)
  have hEfree := ((Scheme.Modules.flat_finitePresentation_locallyFree_fiberRank_tfae E).out 4 2).mp
    (inferInstance : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E)
  apply ((Scheme.Modules.flat_finitePresentation_locallyFree_fiberRank_tfae (cokernel a)).out 2 4).mp
  refine ⟨_root_.isFinitePresentation_of_isCoherent (cokernel a), ?_⟩
  intro x
  letI := TupleEvaluationFiber.residueAlgebra x
  letI := Stacks.SheafOfModules.FlatShortExact.stalkModule (X := X.toRingedSpace) Q x
  letI := Stacks.SheafOfModules.FlatShortExact.stalkModule (X := X.toRingedSpace) E x
  letI := Stacks.SheafOfModules.FlatShortExact.stalkModule (X := X.toRingedSpace) (cokernel a) x
  letI : Module.Finite (X.presheaf.stalk x) (MukaiSaturationRank.Stalk Q x) :=
    Scheme.Modules.finite_stalk_of_isCoherent Q x
  letI : Module.Finite (X.presheaf.stalk x) (MukaiSaturationRank.Stalk E x) :=
    Scheme.Modules.finite_stalk_of_isCoherent E x
  letI : Module.Free (X.presheaf.stalk x) (MukaiSaturationRank.Stalk E x) := hEfree.2 x
  have hinj : Function.Injective
      ((MukaiSaturationRank.stalkMap a x).baseChange (X.residueField x)) := ha x
  exact Module.free_of_lTensor_residueField_injective
    (MukaiSaturationRank.stalkMap a x) (MukaiSaturationRank.stalkMap (cokernel.π a) x)
    (MukaiEvaluationImage.stalkMap_surjective (cokernel.π a) x)
    (MukaiSaturationRank.stalkMap_exact (ShortComplex.cokernelSequence a)
      (ShortComplex.cokernelSequence_exact a) x)
    (by
      simpa only [LinearMap.baseChange_eq_lTensor, Scheme.residueField,
        TupleEvaluationFiber.residueAlgebra, Scheme.residue] using hinj)

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k))

/-- The actual tuple evaluation commutes with the actual native H0
map of the original sheaf morphism. -/
theorem evaluation_naturality {F E : X.Modules} (j : F ⟶ E) {r : ℕ}
    (s : Fin r → cohomologyOverField k f F 0) :
    MukaiSemiIrreducible.evaluation k f F s ≫ j =
      MukaiSemiIrreducible.evaluation k f E
        (fun i => cohomologyOverFieldMap k f j 0 (s i)) := by
  unfold MukaiSemiIrreducible.evaluation
  rw [SheafOfModules.freeHomEquiv_symm_comp]
  congr 1
  funext i
  apply Stacks.PresheafOfModules.sections_ext_top
  change j.app ⊤ ((MukaiSemiIrreducible.sectionOfH0 k f F (s i.down)).eval (op ⊤)) = _
  simp only [MukaiSemiIrreducible.sectionOfH0_eval_top]
  change j.app ⊤ ((cohomologyOverFieldZeroLinearIso k f F).hom (s i.down)) =
    (cohomologyOverFieldZeroLinearIso k f E).hom
      (cohomologyOverFieldMap k f j 0 (s i.down))
  exact (cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap k f j (s i.down)).symm

/-- Surjectivity on actual H0 is surjectivity on the original
compatible global sections, using the actual natural H0 comparison. -/
theorem sectionsMap_surjective_of_h0_surjective {F E : X.Modules} (p : F ⟶ E)
    (hp : Function.Surjective (cohomologyOverFieldMap k f p 0)) :
    Function.Surjective (SheafOfModules.sectionsMap p) := by
  intro s
  obtain ⟨a, ha⟩ := hp ((cohomologyOverFieldZeroLinearIso k f E).inv (s.eval (op ⊤)))
  refine ⟨MukaiSemiIrreducible.sectionOfH0 k f F a, ?_⟩
  apply Stacks.PresheafOfModules.sections_ext_top
  change p.app ⊤ ((MukaiSemiIrreducible.sectionOfH0 k f F a).eval (op ⊤)) = s.eval (op ⊤)
  rw [MukaiSemiIrreducible.sectionOfH0_eval_top]
  calc
    p.app ⊤ ((cohomologyOverFieldZeroLinearIso k f F).hom a) =
        (cohomologyOverFieldZeroLinearIso k f E).hom (cohomologyOverFieldMap k f p 0 a) :=
      (cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap k f p a).symm
    _ = s.eval (op ⊤) := by rw [ha]; exact Iso.inv_hom_id_apply _ _

/-- The actual pair-rank exclusion forbids two sections in any actual
monic line sheaf inside E. No line-subobject exclusion is assumed. -/
theorem h0_le_one_of_mono_rank_one (F E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 1]
    (j : F ⟶ E) [Mono j]
    (hpair : MukaiWedgeKernel.SectionRankExclusion k f E 2 2) :
    Module.finrank k (cohomologyOverField k f F 0) ≤ 1 := by
  by_contra h
  obtain ⟨s, hs⟩ := exists_linearIndependent_of_le_finrank
    (by omega : 2 ≤ Module.finrank k (cohomologyOverField k f F 0))
  let t : Fin 2 → cohomologyOverField k f E 0 :=
    fun i => cohomologyOverFieldMap k f j 0 (s i)
  have ht : LinearIndependent k t :=
    hs.map' (cohomologyOverFieldMap k f j 0).hom
      (LinearMap.ker_eq_bot.mpr
        (MukaiThreeSectionDeterminant.cohomologyMap_injective_of_mono k f j))
  obtain ⟨x, hx⟩ := hpair t ht
  have hr := mapRankAt_factor_le (MukaiSemiIrreducible.evaluation k f F s) j 1 x
  rw [evaluation_naturality] at hr
  change MukaiSemiIrreducible.mapRankAt (MukaiSemiIrreducible.evaluation k f E t) x ≤ 1 at hr
  omega

/-- The actual four-section exclusion bounds sections of every
original rank-two monic subsheaf by three. -/
theorem h0_le_three_of_mono_rank_two (F E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
    (j : F ⟶ E) [Mono j]
    (hfour : MukaiWedgeKernel.SectionRankExclusion k f E 4 3) :
    Module.finrank k (cohomologyOverField k f F 0) ≤ 3 := by
  by_contra h
  obtain ⟨s, hs⟩ := exists_linearIndependent_of_le_finrank
    (by omega : 4 ≤ Module.finrank k (cohomologyOverField k f F 0))
  let t : Fin 4 → cohomologyOverField k f E 0 :=
    fun i => cohomologyOverFieldMap k f j 0 (s i)
  have ht : LinearIndependent k t :=
    hs.map' (cohomologyOverFieldMap k f j 0).hom
      (LinearMap.ker_eq_bot.mpr
        (MukaiThreeSectionDeterminant.cohomologyMap_injective_of_mono k f j))
  obtain ⟨x, hx⟩ := hfour t ht
  have hr := mapRankAt_factor_le (MukaiSemiIrreducible.evaluation k f F s) j 2 x
  rw [evaluation_naturality] at hr
  change MukaiSemiIrreducible.mapRankAt (MukaiSemiIrreducible.evaluation k f E t) x ≤ 2 at hr
  omega

/-- Every putative section of a quotient line would be an actual line
subobject with two sections, forbidden by the original pair exclusion. -/
theorem nonsplit_of_pair_exclusion (E α : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} α 1]
    (hα : 2 ≤ Module.finrank k (cohomologyOverField k f α 0))
    (hpair : MukaiWedgeKernel.SectionRankExclusion k f E 2 2) (p : E ⟶ α) :
    ∀ t : α ⟶ E, t ≫ p ≠ 𝟙 α := by
  intro t ht
  letI : Mono t := mono_of_mono_fac ht
  have hsmall := h0_le_one_of_mono_rank_one k f α E t hpair
  omega

section GenericRank

variable [IsIntegral X]

/-- The rank of the original morphism on the actual generic stalk. -/
def genericMapRank {Q E : X.Modules} (a : Q ⟶ E) : ℕ :=
  Module.finrank (X.presheaf.stalk (genericPoint X))
    (LinearMap.range (MukaiSaturationRank.stalkMap a (genericPoint X)))

/-- A nonzero map into an actual torsion-free target has positive
actual generic rank; the zero-rank alternative would kill the original
morphism by determination at the generic stalk. -/
theorem genericMapRank_pos_of_ne_zero {Q E : X.Modules} [Q.IsCoherent]
    [E.IsQuasicoherent] (hET : IsTorsionFree E) (a : Q ⟶ E) (ha : a ≠ 0) :
    0 < genericMapRank a := by
  letI : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  letI : Module.Finite (X.presheaf.stalk (genericPoint X))
      (MukaiSaturationRank.Stalk Q (genericPoint X)) :=
    Scheme.Modules.finite_stalk_of_isCoherent Q (genericPoint X)
  by_contra hn
  have hz : genericMapRank a = 0 := Nat.eq_zero_of_not_pos hn
  have hbot : LinearMap.range (MukaiSaturationRank.stalkMap a (genericPoint X)) = ⊥ :=
    Submodule.finrank_eq_zero.mp hz
  apply ha
  apply MukaiGenericMono.hom_ext_of_generic_stalkMap_eq hET a 0
  intro m
  rw [MukaiGenericMono.stalkMap_zero]
  simpa only [hbot, Submodule.mem_bot] using
    (LinearMap.mem_range_self (MukaiSaturationRank.stalkMap a (genericPoint X)) m)

variable [IsProper f] (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)

include hreg hdim

/-- A nonzero map from a generated rank-two bundle with no map to O
into a bundle satisfying the actual pair exclusion is generically full
rank, and consequently is an actual sheaf monomorphism. -/
theorem mono_of_generated_no_unit_hom_of_pair_exclusion
    (Q E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 2]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hgen : MukaiSemiIrreducible.GloballyGenerated Q)
    (hvan : ∀ b : Q ⟶ structureModule X, b = 0)
    (hpair : MukaiWedgeKernel.SectionRankExclusion k f E 2 2)
    (a : Q ⟶ E) (ha : a ≠ 0) : Mono a := by
  letI : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} Q :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree Q 2
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 3
  letI : Q.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X Q
  letI : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X E
  letI : Q.IsQuasicoherent := isQuasicoherent_of_isCoherent Q
  letI : E.IsQuasicoherent := isQuasicoherent_of_isCoherent E
  letI : Q.IsFiniteType := _root_.IsCoherent.toIsFiniteType Q
  letI : Module.Finite (X.presheaf.stalk (genericPoint X))
      (MukaiSaturationRank.Stalk Q (genericPoint X)) :=
    Scheme.Modules.finite_stalk_of_isCoherent Q (genericPoint X)
  have hQdim : Module.finrank (X.presheaf.stalk (genericPoint X))
      (MukaiSaturationRank.Stalk Q (genericPoint X)) = 2 :=
    (Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk Q).symm.trans
      (Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank Q 2 (genericPoint X))
  have hle : genericMapRank a ≤ 2 :=
    (MukaiSaturationRank.stalkMap a (genericPoint X)).finrank_range_le.trans_eq hQdim
  have hzero : genericMapRank a ≠ 0 := by
    intro hz
    have hbot : LinearMap.range (MukaiSaturationRank.stalkMap a (genericPoint X)) = ⊥ :=
      Submodule.finrank_eq_zero.mp hz
    have hET : IsTorsionFree E :=
      (isTorsionFree_iff_isFiniteLocallyFree hreg hdim E).mpr inferInstance
    apply ha
    apply MukaiGenericMono.hom_ext_of_generic_stalkMap_eq hET a 0
    intro m
    rw [MukaiGenericMono.stalkMap_zero]
    simpa only [hbot, Submodule.mem_bot] using
      (LinearMap.mem_range_self (MukaiSaturationRank.stalkMap a (genericPoint X)) m)
  have hone : genericMapRank a ≠ 1 := by
    intro h1
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (image a) 1 :=
      MukaiEvaluationImage.image_rank_of_generic_rank a hreg hdim 1 h1
    letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property (image a) :=
      Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace _
    letI := MukaiRecognitionHomBound.finite_bundle_H0 k f (image a) 1
    have htwo := MukaiGeneratedQuotient.two_le_h0_of_generated_no_unit_hom f Q (image a)
      hgen (factorThruImage a) hvan
    have hsmall := h0_le_one_of_mono_rank_one k f (image a) E (image.ι a) hpair
    omega
  have hfull : genericMapRank a = 2 := by omega
  have hsum := (MukaiSaturationRank.stalkMap a (genericPoint X)).finrank_range_add_finrank_ker
  have hker : Module.finrank (X.presheaf.stalk (genericPoint X))
      (LinearMap.ker (MukaiSaturationRank.stalkMap a (genericPoint X))) = 0 := by
    change Module.finrank (X.presheaf.stalk (genericPoint X))
      (LinearMap.range (MukaiSaturationRank.stalkMap a (genericPoint X))) = 2 at hfull
    rw [hfull, hQdim] at hsum
    omega
  have hinj : Function.Injective (MukaiSaturationRank.stalkMap a (genericPoint X)) :=
    LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker)
  apply MukaiGenericMono.mono_of_generic_stalkMap_injective
    ((isTorsionFree_iff_isFiniteLocallyFree hreg hdim Q).mpr inferInstance) a hinj

omit [IsProper f] in
/-- The actual kernel of an epimorphism from a rank-three bundle to a
line has rank two. Local freeness follows from its genuine coherent
torsion-free inclusion, and its rank is calculated at the generic point. -/
theorem kernel_rank_two_of_epi_to_rank_one (E L : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1]
    (q : E ⟶ L) [Epi q] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel q) 2 := by
  letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 3
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} L :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  letI : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X E
  letI : L.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X L
  letI : (kernel q).IsCoherent := _root_.SheafOfModules.kernel_isCoherent q
  letI : E.IsQuasicoherent := isQuasicoherent_of_isCoherent E
  letI : (kernel q).IsQuasicoherent := isQuasicoherent_of_isCoherent (kernel q)
  letI : (kernel q).IsFiniteType := _root_.IsCoherent.toIsFiniteType (kernel q)
  have hET : IsTorsionFree E :=
    (isTorsionFree_iff_isFiniteLocallyFree hreg hdim E).mpr inferInstance
  have hKT : IsTorsionFree (kernel q) :=
    MukaiGeneratedImage.isTorsionFree_of_mono (kernel.ι q) hET
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (kernel q) :=
    (isTorsionFree_iff_isFiniteLocallyFree hreg hdim (kernel q)).mp hKT
  let S := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel q }
  have hadd := Scheme.Modules.fiberRank_genericPoint_add_of_shortExact S hS
  change Scheme.Modules.fiberRank E (genericPoint X) =
    Scheme.Modules.fiberRank (kernel q) (genericPoint X) +
      Scheme.Modules.fiberRank L (genericPoint X) at hadd
  rw [Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank E 3,
    Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank L 1] at hadd
  have hr : Scheme.Modules.fiberRank (kernel q) (genericPoint X) = 2 := by omega
  exact Scheme.Modules.isFiniteLocallyFreeOfRank_of_fiberRank_eq
    (kernel q) 2 (genericPoint X) hr

end GenericRank

section OriginalDualSpan

variable [IsAlgClosed k] [IsProper f] [IsCurve k f] [Smooth f]

omit [IsAlgClosed k] [Smooth f] in
include k f in
/-- A nonzero map from a genuinely generated bundle to the actual
structure sheaf has an actual section. One generating section gives
a nonzero degree-zero endomorphism of O, hence an isomorphism. -/
theorem section_of_nonzero_to_unit_of_globallyGenerated (K : X.Modules)
    (hgen : MukaiSemiIrreducible.GloballyGenerated K)
    (p : K ⟶ structureModule X) (hp : p ≠ 0) :
    ∃ s : structureModule X ⟶ K, s ≫ p = 𝟙 _ := by
  classical
  let O : X.Modules := structureModule X
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property O :=
    Stacks.SheafOfModules.isInvertible_unit _ _
  obtain ⟨g⟩ := hgen
  have hsome : ∃ i : g.I, (SheafOfModules.ιFree i ≫ g.π) ≫ p ≠ 0 := by
    by_contra hn
    push Not at hn
    have hz : g.π ≫ p = 0 := by
      apply O.freeHomEquiv.injective
      funext i
      apply O.unitHomEquiv.symm.injective
      simp only [SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
      simpa only [Category.assoc, comp_zero] using hn i
    apply hp
    apply (cancel_epi g.π).mp
    simpa only [comp_zero] using hz
  obtain ⟨i, hi⟩ := hsome
  let t : O ⟶ K := SheafOfModules.ιFree i ≫ g.π
  letI : IsIso (t ≫ p) :=
    isIso_of_invertibleCurveDegree_eq_of_hom_ne_zero k f
      (IsCurve.topologicalKrullDim_eq_one f).le O O (t ≫ p) hi rfl
  exact ⟨inv (t ≫ p) ≫ t, by simp only [Category.assoc, IsIso.inv_hom_id]⟩

omit [Smooth f] in
/-- A genuinely generated three-section rank-two subbundle of E has
no map to O. A putative map would split, leaving an actual line kernel
with two sections inside E, contrary to the original pair exclusion. -/
theorem hom_unit_eq_zero_of_generated_rank_two_subobject (K E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} K 2]
    (j : K ⟶ E) [Mono j]
    (hgen : MukaiSemiIrreducible.GloballyGenerated K)
    (hK : Module.finrank k (cohomologyOverField k f K 0) = 3)
    (hpair : MukaiWedgeKernel.SectionRankExclusion k f E 2 2)
    (p : K ⟶ structureModule X) : p = 0 := by
  by_contra hp
  let O : X.Modules := structureModule X
  letI := isIso_globalSections_of_isAlgClosed k f
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property O :=
    Stacks.SheafOfModules.isInvertible_unit _ _
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} O 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X O
  obtain ⟨s, hs⟩ := section_of_nonzero_to_unit_of_globallyGenerated k f K hgen p hp
  letI : Epi p := epi_of_epi_fac hs
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel p) 1 :=
    Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi
      p inferInstance 2 1 inferInstance inferInstance
  letI := MukaiRecognitionHomBound.finite_bundle_H0 k f K 2
  letI := MukaiRecognitionHomBound.finite_bundle_H0 k f O 1
  letI := MukaiRecognitionHomBound.finite_bundle_H0 k f (kernel p) 1
  let S := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel p }
  have hH := MukaiBundleUniqueness.finrank_H0_le_add k f hS
  change Module.finrank k (cohomologyOverField k f K 0) ≤
    Module.finrank k (cohomologyOverField k f (kernel p) 0) +
      Module.finrank k (cohomologyOverField k f O 0) at hH
  have hO : Module.finrank k (cohomologyOverField k f O 0) = 1 :=
    finrank_cohomologyOverField_unit_zero_eq_one f
  have hsmall := h0_le_one_of_mono_rank_one k f (kernel p) E (kernel.ι p ≫ j) hpair
  omega

omit [IsAlgClosed k] [IsCurve k f] [Smooth f] in
/-- In any actual rank-three canonical extension with quotient α, the
actual rank-two kernel has top exterior power β. Both tensor products
are compared to the genuine canonical line before cancelling α. -/
def kernelTopExteriorIsoResidual (K E α β : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} K 2]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property α]
    (i : K ⟶ E) (p : E ⟶ α) (w : i ≫ p = 0)
    (hS : (ShortComplex.mk i p w).ShortExact)
    (dE : topExterior E 3 ≅ Stacks.Duality.dualizingSheafOverField f)
    (hres : tensor α β ≅ Stacks.Duality.dualizingSheafOverField f) :
    topExterior K 2 ≅ β := by
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} α 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X α
  let eprod : tensor (topExterior K 2) α ≅ topExterior E 3 :=
    tensorIso (Iso.refl _) (Scheme.Modules.exteriorPowerOneIsoSelf α).symm ≪≫
      Scheme.Modules.exteriorPowerTensorExteriorPowerIso i p w hS 2 0
  let er : tensor β α ≅ Stacks.Duality.dualizingSheafOverField f :=
    Stacks.SheafOfModules.Invertible.tensorProductBraiding X.presheaf X.ringCatSheaf.property β α ≪≫ hres
  exact tensorCancelRightIso α (eprod ≪≫ dE ≪≫ er.symm)

omit [IsAlgClosed k] [IsProper f] in
/-- Semi3 makes the actual three-section basis of any original monic
rank-two subsheaf generate it everywhere. The same argument derives
the original inclusion's actual rank two at every residue fibre. -/
theorem evaluation_epi_and_everywhereRank_of_mono_rank_two_basis (F E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 2]
    (j : F ⟶ E) [Mono j]
    (b : Module.Basis (Fin 3) k (cohomologyOverField k f F 0))
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3) :
    Epi (MukaiSemiIrreducible.evaluation k f F b) ∧
      MukaiSemiIrreducible.EverywhereRank j 2 := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F 2
  letI : F.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X F
  let t : Fin 3 → cohomologyOverField k f E 0 :=
    fun i => cohomologyOverFieldMap k f j 0 (b i)
  have ht : LinearIndependent k t :=
    b.linearIndependent.map' (cohomologyOverFieldMap k f j 0).hom
      (LinearMap.ker_eq_bot.mpr
        (MukaiThreeSectionDeterminant.cohomologyMap_injective_of_mono k f j))
  have hnot : ¬ Mono (MukaiSemiIrreducible.evaluation k f E t) := by
    intro hm
    letI := hm
    have h3 := MukaiSemiExclusions.mapRankAt_generic_of_mono k f E t
    have h2 := mapRankAt_factor_le (MukaiSemiIrreducible.evaluation k f F b) j 2 (genericPoint X)
    rw [evaluation_naturality] at h2
    change MukaiSemiIrreducible.mapRankAt (MukaiSemiIrreducible.evaluation k f E t)
      (genericPoint X) ≤ 2 at h2
    omega
  have hevery : MukaiSemiIrreducible.EverywhereRank
      (MukaiSemiIrreducible.evaluation k f F b ≫ j) 2 := by
    rw [evaluation_naturality]
    rcases hsemi t ht with hm | hevery
    · exact (hnot hm).elim
    · exact hevery
  have hepi : Epi (MukaiSemiIrreducible.evaluation k f F b) := by
    apply epi_of_fiberMap_surjective
    intro x
    letI := TupleEvaluationFiber.residueAlgebra x
    letI := TupleEvaluationFiber.fiberFinite F 2 x
    let ell := MukaiSemiIrreducible.fiberMap (MukaiSemiIrreducible.evaluation k f F b) x
    have h2 := hevery x
    change Module.finrank (X.residueField x)
      (LinearMap.range (MukaiSemiIrreducible.fiberMap
        (MukaiSemiIrreducible.evaluation k f F b ≫ j) x)) = 2 at h2
    rw [fiberMap_comp, LinearMap.range_comp] at h2
    have h2' : Module.finrank (X.residueField x)
        ((LinearMap.range ell).map (MukaiSemiIrreducible.fiberMap j x)) = 2 := h2
    have hle := Submodule.finrank_map_le (MukaiSemiIrreducible.fiberMap j x) (LinearMap.range ell)
    have hb := Submodule.finrank_le (LinearMap.range ell)
    have hdim : Module.finrank (X.residueField x) (MukaiSemiIrreducible.Fiber F x) = 2 :=
      TupleEvaluationFiber.finrank_fiber F 2 x
    have hr : Module.finrank (X.residueField x) (LinearMap.range ell) =
        Module.finrank (X.residueField x) (MukaiSemiIrreducible.Fiber F x) := by omega
    exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq hr)
  refine ⟨hepi, ?_⟩
  letI := hepi
  intro x
  have h := hevery x
  change Module.finrank (X.residueField x)
    (LinearMap.range (TupleEvaluationFiber.inducedFiberMap
      (MukaiSemiIrreducible.evaluation k f F b ≫ j) x)) = 2 at h
  rw [MukaiShortExactFiberRank.range_fiberMap_comp] at h
  exact h

/-- The actual first map in the Hom alternative is monic, derived
from Semi3 and the genuine complete dual span. No monicity or generic
rank of this original morphism is assumed. -/
theorem dualSpan_mono_of_ne_zero (E β : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0))
    (hgen : Epi (netEvaluation β (MukaiDualSpanSections.completeNetSections f β b)))
    (hsections : Module.finrank k (cohomologyOverField k f E 0) = 6)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3)
    (a : dualSpan β (MukaiDualSpanSections.completeNetSections f β b) ⟶ E)
    (ha : a ≠ 0) : Mono a := by
  letI := isIso_globalSections_of_isAlgClosed k f
  letI := MukaiRecognitionHomBound.finite_bundle_H0 k f E 3
  letI := dualSpan_rank β (MukaiDualSpanSections.completeNetSections f β b) hgen
  apply mono_of_generated_no_unit_hom_of_pair_exclusion k f
    (isRegular_of_smooth_over_field f) (IsCurve.topologicalKrullDim_eq_one f).le
    (dualSpan β (MukaiDualSpanSections.completeNetSections f β b)) E
    (MukaiSemiIrreducible.dualSpan_globallyGenerated β
      (MukaiDualSpanSections.completeNetSections f β b) hgen)
    (fun a => (MukaiDualSpanSections.hom_structure_subsingleton_of_complete_net f β b hgen).elim a 0)
    (MukaiSemiExclusions.pair_rank_exclusion k f E hsections hsemi) a ha

/-- For the actual complete dual span, the original nonzero map has
rank two at every point, not merely at the generic point. -/
theorem dualSpan_everywhereRank_two_of_ne_zero
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (E β : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0))
    (hgen : Epi (netEvaluation β (MukaiDualSpanSections.completeNetSections f β b)))
    (hβ : invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le β = 8)
    (hsections : Module.finrank k (cohomologyOverField k f E 0) = 6)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3)
    (a : dualSpan β (MukaiDualSpanSections.completeNetSections f β b) ⟶ E)
    (ha : a ≠ 0) : MukaiSemiIrreducible.EverywhereRank a 2 := by
  let Q := dualSpan β (MukaiDualSpanSections.completeNetSections f β b)
  letI := dualSpan_rank β (MukaiDualSpanSections.completeNetSections f β b) hgen
  letI := MukaiRecognitionHomBound.finite_bundle_H0 k f Q 2
  letI : Mono a := dualSpan_mono_of_ne_zero k f E β b hgen hsections hsemi a ha
  have hQ : Module.finrank k (cohomologyOverField k f Q 0) = 3 :=
    MukaiDualSpanSections.completeDualSpan_h0_eq_three f hnp β b hgen hβ
  let bQ := Module.finBasisOfFinrankEq k (cohomologyOverField k f Q 0) hQ
  exact (evaluation_epi_and_everywhereRank_of_mono_rank_two_basis k f Q E a bQ hsemi).2

/-- The original nonzero dual-span map has an actual invertible
cokernel. Fibre injectivity, local freeness and corank one are all
derived from its proved original everywhere-rank-two property. -/
theorem dualSpan_cokernel_isInvertible_of_ne_zero
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (E β : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0))
    (hgen : Epi (netEvaluation β (MukaiDualSpanSections.completeNetSections f β b)))
    (hβ : invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le β = 8)
    (hsections : Module.finrank k (cohomologyOverField k f E 0) = 6)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3)
    (a : dualSpan β (MukaiDualSpanSections.completeNetSections f β b) ⟶ E)
    (ha : a ≠ 0) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property (cokernel a) := by
  let Q := dualSpan β (MukaiDualSpanSections.completeNetSections f β b)
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 2 :=
    dualSpan_rank β (MukaiDualSpanSections.completeNetSections f β b) hgen
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} Q :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree Q 2
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 3
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : Mono a := dualSpan_mono_of_ne_zero k f E β b hgen hsections hsemi a ha
  have hevery := dualSpan_everywhereRank_two_of_ne_zero k f hnp E β b hgen hβ hsections hsemi a ha
  have hinj (x : X) : Function.Injective (MukaiSemiIrreducible.fiberMap a x) := by
    letI := TupleEvaluationFiber.residueAlgebra x
    letI := TupleEvaluationFiber.fiberFinite Q 2 x
    have hr : Module.finrank (X.residueField x)
        (LinearMap.range (MukaiSemiIrreducible.fiberMap a x)) = 2 := hevery x
    have hs : Module.finrank (X.residueField x) (MukaiSemiIrreducible.Fiber Q x) = 2 :=
      TupleEvaluationFiber.finrank_fiber Q 2 x
    have hd := (MukaiSemiIrreducible.fiberMap a x).finrank_range_add_finrank_ker
    have hd' : Module.finrank (X.residueField x)
        (LinearMap.range (MukaiSemiIrreducible.fiberMap a x)) +
        Module.finrank (X.residueField x) (LinearMap.ker (MukaiSemiIrreducible.fiberMap a x)) = 2 :=
      hd.trans hs
    have hk : Module.finrank (X.residueField x)
        (LinearMap.ker (MukaiSemiIrreducible.fiberMap a x)) = 0 := by omega
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (cokernel a) :=
    cokernel_finiteLocallyFree_of_fiberMap_injective a hinj
  letI : Q.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X Q
  letI : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X E
  letI : (cokernel a).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X (cokernel a)
  letI : (cokernel a).IsFiniteType := _root_.IsCoherent.toIsFiniteType (cokernel a)
  let S := ShortComplex.mk a (cokernel.π a) (cokernel.condition a)
  have hS : S.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact a
      mono_f := by change Mono a; infer_instance
      epi_g := by change Epi (cokernel.π a); infer_instance }
  have hadd := Scheme.Modules.fiberRank_genericPoint_add_of_shortExact S hS
  change Scheme.Modules.fiberRank E (genericPoint X) =
    Scheme.Modules.fiberRank Q (genericPoint X) +
      Scheme.Modules.fiberRank (cokernel a) (genericPoint X) at hadd
  rw [Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank E 3,
    Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank Q 2] at hadd
  have hr : Scheme.Modules.fiberRank (cokernel a) (genericPoint X) = 1 := by omega
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (cokernel a) 1 :=
    Scheme.Modules.isFiniteLocallyFreeOfRank_of_fiberRank_eq (cokernel a) 1 (genericPoint X) hr
  exact Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace _

/-- The first Hom branch produces the actual required extension.
The original cokernel line is identified with α by the actual canonical
determinant and residual isomorphisms. Gamma-splitting and nonsplitting
then follow from actual section counts and the original pair exclusion. -/
theorem extension_of_nonzero_dualSpan
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (E α β : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property α]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (bα : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f α 0))
    (bβ : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0))
    (hgenβ : Epi (netEvaluation β (MukaiDualSpanSections.completeNetSections f β bβ)))
    (hβ : invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le β = 8)
    (hsections : Module.finrank k (cohomologyOverField k f E 0) = 6)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3)
    (dE : topExterior E 3 ≅ Stacks.Duality.dualizingSheafOverField f)
    (hres : tensor α β ≅ Stacks.Duality.dualizingSheafOverField f)
    (a : dualSpan β (MukaiDualSpanSections.completeNetSections f β bβ) ⟶ E)
    (ha : a ≠ 0) :
    ∃ (p : E ⟶ α) (w : a ≫ p = 0),
      (ShortComplex.mk a p w).ShortExact ∧
        Function.Surjective (SheafOfModules.sectionsMap p) ∧
        (∀ t : α ⟶ E, t ≫ p ≠ 𝟙 α) := by
  let Q := dualSpan β (MukaiDualSpanSections.completeNetSections f β bβ)
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 2 :=
    dualSpan_rank β (MukaiDualSpanSections.completeNetSections f β bβ) hgenβ
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} α 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X α
  letI : Mono a := dualSpan_mono_of_ne_zero k f E β bβ hgenβ hsections hsemi a ha
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property (cokernel a) :=
    dualSpan_cokernel_isInvertible_of_ne_zero k f hnp E β bβ hgenβ hβ hsections hsemi a ha
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (cokernel a) 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X (cokernel a)
  let S := ShortComplex.mk a (cokernel.π a) (cokernel.condition a)
  have hS : S.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact a
      mono_f := by change Mono a; infer_instance
      epi_g := by change Epi (cokernel.π a); infer_instance }
  let eprod : topExterior E 3 ≅ tensor (cokernel a) β :=
    MukaiDualSpanDeterminant.extensionTopExteriorIso β (cokernel a)
      (MukaiDualSpanSections.completeNetSections f β bβ) hgenβ
      a (cokernel.π a) (cokernel.condition a) hS
  let eC : cokernel a ≅ α := tensorCancelRightIso β (eprod.symm ≪≫ dE ≪≫ hres.symm)
  let p : E ⟶ α := cokernel.π a ≫ eC.hom
  have w : a ≫ p = 0 := by simp [p, ← Category.assoc]
  let T := ShortComplex.mk a p w
  let eT : S ≅ T := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) eC
    (by simp [S, T]) (by simp [S, T, p])
  have hT : T.ShortExact := ShortComplex.shortExact_of_iso eT hS
  letI := MukaiRecognitionHomBound.finite_bundle_H0 k f Q 2
  letI := MukaiRecognitionHomBound.finite_bundle_H0 k f E 3
  letI := MukaiRecognitionHomBound.finite_bundle_H0 k f α 1
  have hQ0 : Module.finrank k (cohomologyOverField k f Q 0) = 3 :=
    MukaiDualSpanSections.completeDualSpan_h0_eq_three f hnp β bβ hgenβ hβ
  have hα0 : Module.finrank k (cohomologyOverField k f α 0) = 3 := by
    simpa using Module.finrank_eq_card_basis bα
  have hγ := (MukaiBundleUniqueness.gammaSplit_iff_H0_six k f hT hQ0 hα0).2 hsections
  exact ⟨p, w, hT, hγ, nonsplit_of_pair_exclusion k f E α (by omega)
    (MukaiSemiExclusions.pair_rank_exclusion k f E hsections hsemi) p⟩

/-- A nonzero actual map from E to a degree-eight line is epimorphic.
A proper image would have degree at most seven, hence at most two
sections; the actual rank-two kernel would then have four sections,
contradicting the original Semi3 four-section exclusion. -/
theorem epi_to_degree_eight_line_of_ne_zero (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (E α : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property α]
    (hα : invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le α = 8)
    (hsections : Module.finrank k (cohomologyOverField k f E 0) = 6)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3)
    (g : E ⟶ α) (hg0 : g ≠ 0) : Epi g := by
  let hreg := isRegular_of_smooth_over_field f
  let hdim := (IsCurve.topologicalKrullDim_eq_one f).le
  letI : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  letI : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E 3
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} α 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X α
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} α :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree α 1
  letI : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X E
  letI : α.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X α
  letI : α.IsQuasicoherent := isQuasicoherent_of_isCoherent α
  letI : α.IsFiniteType := _root_.IsCoherent.toIsFiniteType α
  letI : Module.Finite (X.presheaf.stalk (genericPoint X))
      (MukaiSaturationRank.Stalk α (genericPoint X)) :=
    Scheme.Modules.finite_stalk_of_isCoherent α (genericPoint X)
  letI := MukaiRecognitionHomBound.finite_bundle_H0 k f E 3
  have hαdim : Module.finrank (X.presheaf.stalk (genericPoint X))
      (MukaiSaturationRank.Stalk α (genericPoint X)) = 1 :=
    (Scheme.Modules.fiberRank_genericPoint_eq_finrank_stalk α).symm.trans
      (Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank α 1 (genericPoint X))
  have hpos := genericMapRank_pos_of_ne_zero
    ((isTorsionFree_iff_isFiniteLocallyFree hreg hdim α).mpr inferInstance) g hg0
  have hle : genericMapRank g ≤ 1 :=
    (Submodule.finrank_le (LinearMap.range (MukaiSaturationRank.stalkMap g (genericPoint X)))).trans_eq hαdim
  have hgr : genericMapRank g = 1 := by omega
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (image g) 1 :=
    MukaiEvaluationImage.image_rank_of_generic_rank g hreg hdim 1 hgr
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property (image g) :=
    Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace _
  letI := MukaiRecognitionHomBound.finite_bundle_H0 k f (image g) 1
  by_contra hn
  have hinc : image.ι g ≠ 0 := by
    intro hz
    apply hg0
    rw [← image.fac g, hz, comp_zero]
  have hdeg : invertibleCurveDegree k f hdim (image g) ≤ 7 := by
    have hb := invertibleCurveDegree_le_of_hom_ne_zero k f hdim (image g) α (image.ι g) hinc
    rw [hα] at hb
    have hne : invertibleCurveDegree k f hdim (image g) ≠ 8 := by
      intro heq
      letI : IsIso (image.ι g) :=
        isIso_of_invertibleCurveDegree_eq_of_hom_ne_zero k f hdim (image g) α (image.ι g)
          hinc (by rw [heq, hα])
      apply hn
      rw [← image.fac g]
      infer_instance
    omega
  have hI := MukaiNoDegreeSevenNet.h0_le_two_of_degree_le_seven f hdim hg hnp (image g) hdeg
  let q := factorThruImage g
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel q) 2 :=
    kernel_rank_two_of_epi_to_rank_one hreg hdim E (image g) q
  letI := MukaiRecognitionHomBound.finite_bundle_H0 k f (kernel q) 2
  let S := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel q }
  have hH := MukaiBundleUniqueness.finrank_H0_le_add k f hS
  change Module.finrank k (cohomologyOverField k f E 0) ≤
    Module.finrank k (cohomologyOverField k f (kernel q) 0) +
      Module.finrank k (cohomologyOverField k f (image g) 0) at hH
  have hsmall := h0_le_three_of_mono_rank_two k f (kernel q) E (kernel.ι q)
    (MukaiSemiExclusions.four_rank_exclusion k f E hsemi)
  omega

/-- The original nonzero quotient to a complete degree-eight net has
an actual rank-two, three-section kernel; its original short exact
sequence is nonsplit and genuinely surjective on global sections.
Identification of this actual kernel with Qβ is a subsequent step. -/
theorem actual_kernel_extension_of_ne_zero_to_complete_net (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (E α : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property α]
    (bα : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f α 0))
    (hα : invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le α = 8)
    (hsections : Module.finrank k (cohomologyOverField k f E 0) = 6)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3)
    (g : E ⟶ α) (hg0 : g ≠ 0) :
    Epi g ∧ SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel g) 2 ∧
      Module.finrank k (cohomologyOverField k f (kernel g) 0) = 3 ∧
      Function.Surjective (SheafOfModules.sectionsMap g) ∧
      (∀ t : α ⟶ E, t ≫ g ≠ 𝟙 α) := by
  let hreg := isRegular_of_smooth_over_field f
  let hdim := (IsCurve.topologicalKrullDim_eq_one f).le
  letI := epi_to_degree_eight_line_of_ne_zero k f hg hnp E α hα hsections hsemi g hg0
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} α 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X α
  let hK := kernel_rank_two_of_epi_to_rank_one hreg hdim E α g
  letI := hK
  letI := MukaiRecognitionHomBound.finite_bundle_H0 k f E 3
  letI := MukaiRecognitionHomBound.finite_bundle_H0 k f α 1
  letI := MukaiRecognitionHomBound.finite_bundle_H0 k f (kernel g) 2
  have hα0 : Module.finrank k (cohomologyOverField k f α 0) = 3 := by
    simpa using Module.finrank_eq_card_basis bα
  let S := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel g }
  have hH := MukaiBundleUniqueness.finrank_H0_le_add k f hS
  change Module.finrank k (cohomologyOverField k f E 0) ≤
    Module.finrank k (cohomologyOverField k f (kernel g) 0) +
      Module.finrank k (cohomologyOverField k f α 0) at hH
  have hsmall := h0_le_three_of_mono_rank_two k f (kernel g) E (kernel.ι g)
    (MukaiSemiExclusions.four_rank_exclusion k f E hsemi)
  have hK0 : Module.finrank k (cohomologyOverField k f (kernel g) 0) = 3 := by omega
  refine ⟨inferInstance, hK, hK0, ?_, ?_⟩
  · obtain ⟨δ, hinj, hex, _, _⟩ := exists_cohomologyOverField_longExactSequence k f hS
    let p0 := (cohomologyOverFieldMap k f g 0).hom
    have hd := p0.finrank_range_add_finrank_ker
    rw [(hex 0).linearMap_ker_eq, LinearMap.finrank_range_of_inj hinj] at hd
    change Module.finrank k (LinearMap.range p0) +
      Module.finrank k (cohomologyOverField k f (kernel g) 0) =
      Module.finrank k (cohomologyOverField k f E 0) at hd
    have hr : Module.finrank k (LinearMap.range p0) =
        Module.finrank k (cohomologyOverField k f α 0) := by omega
    have hsurj : Function.Surjective p0 :=
      LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq hr)
    exact sectionsMap_surjective_of_h0_surjective k f g hsurj
  · exact nonsplit_of_pair_exclusion k f E α (by omega)
      (MukaiSemiExclusions.pair_rank_exclusion k f E hsections hsemi) g

/-- The actual kernel in the second Hom branch is genuinely globally
generated. Its complete three-section evaluation is proved epi by
Semi3; no generation premise for that kernel is supplied. -/
theorem kernel_globallyGenerated_of_ne_zero_to_complete_net (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (E α : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property α]
    (bα : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f α 0))
    (hα : invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le α = 8)
    (hsections : Module.finrank k (cohomologyOverField k f E 0) = 6)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3)
    (g : E ⟶ α) (hg0 : g ≠ 0) : MukaiSemiIrreducible.GloballyGenerated (kernel g) := by
  obtain ⟨hepi, hK, hK0, _, _⟩ :=
    actual_kernel_extension_of_ne_zero_to_complete_net k f hg hnp E α bα hα hsections hsemi g hg0
  letI := hepi
  letI := hK
  letI := MukaiRecognitionHomBound.finite_bundle_H0 k f (kernel g) 2
  let bK := Module.finBasisOfFinrankEq k (cohomologyOverField k f (kernel g) 0) hK0
  have hδ := (evaluation_epi_and_everywhereRank_of_mono_rank_two_basis
    k f (kernel g) E (kernel.ι g) bK hsemi).1
  exact ⟨⟨ULift.{u} (Fin 3), fun i => MukaiSemiIrreducible.sectionOfH0 k f (kernel g) (bK i.down), hδ⟩⟩

/-- The second Hom branch gives the actual original dual-span
extension. Its kernel's generation, determinant and lack of a trivial
quotient are derived before applying actual three-generator recognition. -/
theorem extension_of_nonzero_to_complete_net (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (E α β : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property α]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property β]
    (bα : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f α 0))
    (bβ : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f β 0))
    (hα : invertibleCurveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le α = 8)
    (hsections : Module.finrank k (cohomologyOverField k f E 0) = 6)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3)
    (dE : topExterior E 3 ≅ Stacks.Duality.dualizingSheafOverField f)
    (hres : tensor α β ≅ Stacks.Duality.dualizingSheafOverField f)
    (g : E ⟶ α) (hg0 : g ≠ 0) :
    ∃ (i : dualSpan β (MukaiDualSpanSections.completeNetSections f β bβ) ⟶ E)
      (w : i ≫ g = 0), (ShortComplex.mk i g w).ShortExact ∧
        Function.Surjective (SheafOfModules.sectionsMap g) ∧
        (∀ t : α ⟶ E, t ≫ g ≠ 𝟙 α) := by
  letI := isIso_globalSections_of_isAlgClosed k f
  obtain ⟨hepi, hK, hK0, hγ, hn⟩ :=
    actual_kernel_extension_of_ne_zero_to_complete_net k f hg hnp E α bα hα hsections hsemi g hg0
  letI := hepi
  letI := hK
  letI := MukaiRecognitionHomBound.finite_bundle_H0 k f E 3
  letI := MukaiRecognitionHomBound.finite_bundle_H0 k f (kernel g) 2
  let bK := Module.finBasisOfFinrankEq k (cohomologyOverField k f (kernel g) 0) hK0
  let q : netFree X ⟶ kernel g := MukaiSemiIrreducible.evaluation k f (kernel g) bK
  letI : Epi q :=
    (evaluation_epi_and_everywhereRank_of_mono_rank_two_basis k f (kernel g) E (kernel.ι g) bK hsemi).1
  let S := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel g }
  let hdet := kernelTopExteriorIsoResidual k f (kernel g) E α β (kernel.ι g) g
    (kernel.condition g) hS dE hres
  have hgenK := kernel_globallyGenerated_of_ne_zero_to_complete_net
    k f hg hnp E α bα hα hsections hsemi g hg0
  have hvan : ∀ p : kernel g ⟶ structureModule X, p = 0 :=
    hom_unit_eq_zero_of_generated_rank_two_subobject k f (kernel g) E (kernel.ι g)
      hgenK hK0 (MukaiSemiExclusions.pair_rank_exclusion k f E hsections hsemi)
  let eK := MukaiThreeGeneratorRecognition.dualSpanIso_of_three_generators k f
    (kernel g) β q hdet hvan bβ
  let i : dualSpan β (MukaiDualSpanSections.completeNetSections f β bβ) ⟶ E :=
    eK.inv ≫ kernel.ι g
  have w : i ≫ g = 0 := by simp [i, Category.assoc]
  let T := ShortComplex.mk i g w
  let eT : S ≅ T := ShortComplex.isoMk eK (Iso.refl _) (Iso.refl _)
    (by simp [S, T, i]) (by simp [S, T])
  exact ⟨i, w, ShortComplex.shortExact_of_iso eT hS, hγ, hn⟩

/-- Actual recognition in the six-section, globally generated form
needed for M9. The input nets and all maps are genuine native ones.
No Mono/Epi, image rank, kernel identification or classification
premise is supplied. This does not assert the h0≥6 version of Lemma5.5. -/
theorem exists_nonsplit_gammaSplit_extension_of_semi
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (A B : LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 8 2)
    (bA : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f A.L 0))
    (bB : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f B.L 0))
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (hsections : Module.finrank k (cohomologyOverField k f E 0) = 6)
    (_hgenE : MukaiSemiIrreducible.GloballyGenerated E)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3)
    (dE : topExterior E 3 ≅ Stacks.Duality.dualizingSheafOverField f)
    (hres : tensor A.L B.L ≅ Stacks.Duality.dualizingSheafOverField f) :
    ∃ (i : dualSpan B.L (MukaiDualSpanSections.completeNetSections f B.L bB) ⟶ E)
      (p : E ⟶ A.L) (w : i ≫ p = 0),
      (ShortComplex.mk i p w).ShortExact ∧
        Function.Surjective (SheafOfModules.sectionsMap p) ∧
        ¬ Nonempty (ShortComplex.mk i p w).Splitting := by
  letI := A.isInvertible
  letI := B.isInvertible
  letI := isIso_globalSections_of_isAlgClosed k f
  have hno7 := MukaiNoDegreeSevenNet.no_net_of_degree_le_seven f
    (IsCurve.topologicalKrullDim_eq_one f).le hg hnp
  have hgenB := MukaiCompleteEvaluation.degree_eight_completeNetEvaluation_epi f
    (IsCurve.topologicalKrullDim_eq_one f).le hno7 B bB
  let dDet : Scheme.Modules.determinant E ≅ Stacks.Duality.dualizingSheafOverField f :=
    (Scheme.Modules.exteriorPowerIsoDeterminant E 3).symm ≪≫ dE
  have hAlt := MukaiRecognitionHomBound.nonzero_hom_alternative_complete_net k f hg E A.L B.L
    bB hgenB hres dDet B.degree_eq (by omega)
  rcases hAlt with ⟨a, ha⟩ | ⟨g, hg0⟩
  · obtain ⟨p, w, hS, hγ, hn⟩ := extension_of_nonzero_dualSpan k f hnp E A.L B.L
      bA bB hgenB B.degree_eq hsections hsemi dE hres a ha
    refine ⟨a, p, w, hS, hγ, ?_⟩
    rintro ⟨sp⟩
    exact hn sp.s sp.s_g
  · obtain ⟨i, w, hS, hγ, hn⟩ := extension_of_nonzero_to_complete_net k f hg hnp E A.L B.L
      bA bB A.degree_eq hsections hsemi dE hres g hg0
    refine ⟨i, g, w, hS, hγ, ?_⟩
    rintro ⟨sp⟩
    exact hn sp.s sp.s_g

/-- The same actual recognition theorem for the native annihilator
determinant, transported by the genuine top-exterior comparison. -/
theorem exists_nonsplit_gammaSplit_extension_of_canonicalDeterminant
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (A B : LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 8 2)
    (bA : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f A.L 0))
    (bB : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f B.L 0))
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (hsections : Module.finrank k (cohomologyOverField k f E 0) = 6)
    (hgenE : MukaiSemiIrreducible.GloballyGenerated E)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3)
    (dE : Scheme.Modules.determinant E ≅ Stacks.Duality.dualizingSheafOverField f)
    (hres : tensor A.L B.L ≅ Stacks.Duality.dualizingSheafOverField f) :
    ∃ (i : dualSpan B.L (MukaiDualSpanSections.completeNetSections f B.L bB) ⟶ E)
      (p : E ⟶ A.L) (w : i ≫ p = 0),
      (ShortComplex.mk i p w).ShortExact ∧
        Function.Surjective (SheafOfModules.sectionsMap p) ∧
        ¬ Nonempty (ShortComplex.mk i p w).Splitting :=
  exists_nonsplit_gammaSplit_extension_of_semi k f hg hnp A B bA bB E hsections hgenE hsemi
    (Scheme.Modules.exteriorPowerIsoDeterminant E 3 ≪≫ dE) hres

end OriginalDualSpan

end M9Native.MukaiBundleRecognition
