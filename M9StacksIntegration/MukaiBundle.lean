/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

The Ext lifting argument below is adapted from the native Ext exact-sequence
API and its private lifting lemma. The other constructions specialize native
sheaves of modules to the first step of Mukai's construction.
-/
module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.KernelConstantRank
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Modules.DualFreeFinite
public import StacksFrontier.AlgebraicGeometry.Modules.DualShortExact
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Extension
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeries
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic.ExtOneAndVanishing
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# The native evaluation-kernel step in Mukai's genus-nine construction

For three globally generating sections of an actual invertible sheaf `β`,
`evaluationKernel β s` is the categorical kernel of their evaluation map and
`dualSpan β s` is its actual sheaf dual. We prove that both have rank two,
and expose the short exact evaluation sequence and its actual dual sequence.

We also realize an actual native Ext¹ class as a short exact sequence and
prove the precise Γ-splitting criterion: every global section of the quotient
lifts if and only if pullback of the Ext class along every `𝒪_X ⟶ α` vanishes.
Consequently a class with this property produces an actual rank-three sheaf
when its end terms have ranks two and one.

This file does not assert existence of the nonzero Γ-split class used in
Mukai's Lemma 5.2. That requires the geometric vanishing in Lemma 5.1 and
the parity result of Proposition 1.2. Nor does a degree-eight linear series
alone establish that its complete evaluation map is epimorphic. These are
separate inputs to the constructions below.

Reference: S. Mukai, *Curves and symmetric spaces, II*, Annals of Mathematics
172 (2010), §§1 and 5, especially (1.1), (5.3), and Lemma 5.2.
https://annals.math.princeton.edu/wp-content/uploads/annals-v172-n3-p01-p.pdf

Native Lean 4.35.0 verification and axiom-audit results are recorded in
`audits/mukai-bundle/README.md`; geometric obligations remain as listed above.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Abelian
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.MukaiBundle

variable {X : Scheme.{u}}

/-- The structure sheaf at the native `X.Modules` spelling. This keeps
Ext and sheaf morphisms in the same abelian category. -/
abbrev structureModule (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

/-- Three copies of the actual structure sheaf, with the index in the
same universe as the scheme's modules. -/
def netFree (X : Scheme.{u}) : X.Modules :=
  SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 3))

/-- Evaluation of three actual global sections of `β`. -/
def netEvaluation (β : X.Modules) (s : ULift.{u} (Fin 3) → β.sections) :
    netFree X ⟶ β :=
  β.freeHomEquiv.symm s

/-- The evaluation sends each tautological section to the chosen section. -/
theorem netEvaluation_freeSection (β : X.Modules)
    (s : ULift.{u} (Fin 3) → β.sections) (i : ULift.{u} (Fin 3)) :
    SheafOfModules.sectionsMap (netEvaluation β s)
      (SheafOfModules.freeSection i) = s i :=
  SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection s i

/-- The actual kernel, before dualizing. -/
def evaluationKernel (β : X.Modules) (s : ULift.{u} (Fin 3) → β.sections) : X.Modules :=
  kernel (netEvaluation β s)

/-- The actual kernel inclusion. -/
def evaluationKernelInclusion (β : X.Modules)
    (s : ULift.{u} (Fin 3) → β.sections) : evaluationKernel β s ⟶ netFree X :=
  kernel.ι (netEvaluation β s)

/-- The actual evaluation complex. -/
def evaluationSequence (β : X.Modules) (s : ULift.{u} (Fin 3) → β.sections) :
    ShortComplex X.Modules :=
  ShortComplex.mk (evaluationKernelInclusion β s) (netEvaluation β s)
    (kernel.condition (netEvaluation β s))

/-- Global generation makes the categorical evaluation sequence short exact. -/
theorem evaluationSequence_shortExact (β : X.Modules)
    (s : ULift.{u} (Fin 3) → β.sections) (hgen : Epi (netEvaluation β s)) :
    (evaluationSequence β s).ShortExact := by
  let := hgen
  exact {
    exact := ShortComplex.exact_kernel (netEvaluation β s)
    mono_f := inferInstanceAs (Mono (kernel.ι (netEvaluation β s)))
    epi_g := hgen }

/-- The source of the actual evaluation map has rank three. -/
theorem netFree_rank (X : Scheme.{u}) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (netFree X) 3 :=
  SheafOfModules.isFiniteLocallyFreeOfRank_free_of_equiv
    (ULift.{u} (Fin 3)) 3 Equiv.ulift

/-- The kernel of a globally generated net in a line bundle has rank two.
The rank is deduced from the actual kernel and evaluation map. -/
theorem evaluationKernel_rank (β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    (s : ULift.{u} (Fin 3) → β.sections) (hgen : Epi (netEvaluation β s)) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (evaluationKernel β s) 2 :=
  Stacks.ProjectiveBundleSplitting.isFiniteLocallyFreeOfRank_kernel_of_epi_isInvertible_pred
    (netEvaluation β s) hgen inferInstance 2 (netFree_rank X)

/-- Mukai's `Q_β`: the actual dual of the actual evaluation kernel. -/
def dualSpan (β : X.Modules) (s : ULift.{u} (Fin 3) → β.sections) : X.Modules :=
  dualSheaf (evaluationKernel β s)

/-- Mukai's dual-span sheaf is a genuine vector bundle of rank two. -/
theorem dualSpan_rank (β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    (s : ULift.{u} (Fin 3) → β.sections) (hgen : Epi (netEvaluation β s)) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (dualSpan β s) 2 :=
  isFiniteLocallyFreeOfRank_dualSheaf (evaluationKernel β s) 2
    (evaluationKernel_rank β s hgen)

/-- The dual of the free rank-three evaluation source is the actual free
rank-three sheaf. -/
def dualNetFreeIso (X : Scheme.{u}) : dualSheaf (netFree X) ≅ netFree X :=
  dualSheafFreeIso X (ULift.{u} (Fin 3))

/-- The actual dual evaluation sequence is short exact. This is (1.1)
dualized; its middle term is identified with `𝒪_X³` by `dualNetFreeIso`. -/
theorem dualEvaluationSequence_shortExact (β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    (s : ULift.{u} (Fin 3) → β.sections) (hgen : Epi (netEvaluation β s)) :
    ∃ w : dualMap (netEvaluation β s) ≫ dualMap (evaluationKernelInclusion β s) = 0,
      (ShortComplex.mk (dualMap (netEvaluation β s))
        (dualMap (evaluationKernelInclusion β s)) w).ShortExact := by
  have hS := evaluationSequence_shortExact β s hgen
  have hkernel := (evaluationKernel_rank β s hgen).isFiniteLocallyFree
  have hfree := (netFree_rank X).isFiniteLocallyFree
  have hβ := (SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X β).isFiniteLocallyFree
  exact exists_dualSheaf_shortExact (evaluationKernelInclusion β s) (netEvaluation β s)
    (kernel.condition (netEvaluation β s)) hS.mono_f hS.epi_g hS.exact
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2 hkernel)
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2 hfree)
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2 hβ)

/-- Constant ranks add in an actual extension, with the middle rank
established locally rather than assumed. -/
theorem extension_rank (S : ShortComplex X.Modules) (hS : S.ShortExact) (a c : ℕ)
    (h₁ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₁ a)
    (h₃ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₃ c) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} S.X₂ (a + c) := by
  have h₂' := Stacks.FiniteLocallyFree.isFiniteLocallyFree_of_shortExact S hS
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2
      h₁.isFiniteLocallyFree)
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2
      h₃.isFiniteLocallyFree)
  have h₂ : SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₂ :=
    (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).1 h₂'
  choose U hx r hr using fun x : X ↦
    Stacks.ProjectiveBundleSplitting.exists_isFiniteLocallyFreeOfRank_restrict S.X₂ h₂ x
  refine (Scheme.Modules.isFiniteLocallyFreeOfRank_iff S.X₂ (a + c)).mp ?_
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_iSup_eq_top U ?_ fun x ↦ ?_
  · refine eq_top_iff.mpr fun y _ ↦ ?_
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨y, hx y⟩
  · let G := Scheme.Modules.restrictFunctor (U x).ι
    have hS' : (S.map G).ShortExact := hS.map_of_exact G
    let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.map G).X₁ a :=
      (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mp
        (((Scheme.Modules.isFiniteLocallyFreeOfRank_iff S.X₁ a).mpr h₁).restrict (U x).ι)
    let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.map G).X₂ (r x) := hr x
    let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (S.map G).X₃ c :=
      (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mp
        (((Scheme.Modules.isFiniteLocallyFreeOfRank_iff S.X₃ c).mpr h₃).restrict (U x).ι)
    have heq := SheafOfModules.rank_add_of_shortExact (S.map G) hS' a (r x) c
      (⟨x, hx x⟩ : (U x).toScheme)
    exact (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ _).mpr (heq ▸ hr x)

/-! Native Ext is small here because the actual sheaf category is a
locally small Grothendieck abelian category with enough injectives. -/

local instance nativeHasExt (X : Scheme.{u}) : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules

/-- Lifting an actual morphism through an actual extension is equivalent
to annihilating its native Ext class. -/
theorem lifts_iff_extClass_zero {T : X.Modules} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (s : T ⟶ S.X₃) :
    (∃ t : T ⟶ S.X₂, t ≫ S.g = s) ↔
      (Ext.mk₀ s).comp hS.extClass (zero_add 1) = 0 := by
  constructor
  · rintro ⟨t, rfl⟩
    rw [← Ext.mk₀_comp_mk₀_assoc, hS.comp_extClass, Ext.comp_zero]
  · intro h
    obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ T hS (Ext.mk₀ s) (zero_add 1) h
    obtain ⟨t, rfl⟩ := (Ext.mk₀_bijective T S.X₂).surjective x
    exact ⟨t, (Ext.mk₀_bijective T S.X₃).injective (by rwa [Ext.mk₀_comp_mk₀] at hx)⟩

/-- Γ-splitting is precisely the vanishing of pullback of the native
extension class along every actual global section of the quotient. -/
theorem gammaSplit_iff_extClass_zero {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    Function.Surjective (SheafOfModules.sectionsMap S.g) ↔
      ∀ s : structureModule X ⟶ S.X₃,
        (Ext.mk₀ s).comp hS.extClass (zero_add 1) = 0 := by
  constructor
  · intro h s
    obtain ⟨t, ht⟩ := h (S.X₃.unitHomEquiv s)
    apply (lifts_iff_extClass_zero hS s).1
    refine ⟨S.X₂.unitHomEquiv.symm t, ?_⟩
    exact (SheafOfModules.unitHomEquiv_symm_comp t S.g).trans
      ((congrArg S.X₃.unitHomEquiv.symm ht).trans
        (S.X₃.unitHomEquiv.symm_apply_apply s))
  · intro h s
    obtain ⟨t, ht⟩ := (lifts_iff_extClass_zero hS (S.X₃.unitHomEquiv.symm s)).2 (h _)
    refine ⟨S.X₂.unitHomEquiv t, ?_⟩
    exact (SheafOfModules.unitHomEquiv_comp_apply t S.g).symm.trans
      ((congrArg S.X₃.unitHomEquiv ht).trans (S.X₃.unitHomEquiv.apply_symm_apply s))

/-- A nonzero native extension class rules out a splitting of the actual
short exact sequence. -/
theorem not_nonempty_splitting_of_extClass_ne_zero {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (hclass : hS.extClass ≠ 0) : ¬ Nonempty S.Splitting := by
  rintro ⟨sp⟩
  have hzero := (lifts_iff_extClass_zero hS (𝟙 S.X₃)).1 ⟨sp.s, sp.s_g⟩
  exact hclass (by simpa using hzero)

/-- A native Ext class satisfying the actual section-lifting condition
constructs an actual Γ-split extension of a rank-one sheaf by a rank-two
sheaf. The rank-three middle term is produced by Ext realization. -/
theorem exists_rankThree_gammaSplit_extension (Q α : X.Modules)
    (hQ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Q 2)
    (hα : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} α 1)
    (ξ : Ext.{u} α Q 1)
    (hξ : ∀ s : structureModule X ⟶ α,
      (Ext.mk₀ s).comp ξ (zero_add 1) = 0) :
    ∃ (E : X.Modules) (i : Q ⟶ E) (p : E ⟶ α) (w : i ≫ p = 0)
      (hS : (ShortComplex.mk i p w).ShortExact),
      hS.extClass = ξ ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 3 ∧
      Function.Surjective (SheafOfModules.sectionsMap p) := by
  obtain ⟨E, i, p, w, hS, hclass⟩ :=
    (Ext.extClass_surjective_and_eq_iff_iso_and_baerSum X.Modules α Q).1 ξ
  refine ⟨E, i, p, w, hS, hclass, extension_rank _ hS 2 1 hQ hα, ?_⟩
  exact (gammaSplit_iff_extClass_zero hS).2 (by simpa only [hclass] using hξ)

/-- Specializing the preceding construction to the actual dual-span
bundle constructed from a globally generated net. -/
theorem exists_dualSpan_extension (β α : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 α]
    (s : ULift.{u} (Fin 3) → β.sections) (hgen : Epi (netEvaluation β s))
    (ξ : Ext.{u} α (dualSpan β s) 1)
    (hξ : ∀ t : structureModule X ⟶ α,
      (Ext.mk₀ t).comp ξ (zero_add 1) = 0) :
    ∃ (E : X.Modules) (i : dualSpan β s ⟶ E) (p : E ⟶ α) (w : i ≫ p = 0)
      (hS : (ShortComplex.mk i p w).ShortExact),
      hS.extClass = ξ ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 3 ∧
      Function.Surjective (SheafOfModules.sectionsMap p) :=
  exists_rankThree_gammaSplit_extension (dualSpan β s) α
    (dualSpan_rank β s hgen)
    (SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X α) ξ hξ

/-- A nonzero Γ-split class produces an actual nonsplit rank-three
extension, with no middle bundle assumed in the input. -/
theorem exists_nonsplit_dualSpan_extension (β α : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 α]
    (s : ULift.{u} (Fin 3) → β.sections) (hgen : Epi (netEvaluation β s))
    (ξ : Ext.{u} α (dualSpan β s) 1) (hne : ξ ≠ 0)
    (hξ : ∀ t : structureModule X ⟶ α,
      (Ext.mk₀ t).comp ξ (zero_add 1) = 0) :
    ∃ (E : X.Modules) (i : dualSpan β s ⟶ E) (p : E ⟶ α) (w : i ≫ p = 0)
      (hS : (ShortComplex.mk i p w).ShortExact),
      hS.extClass = ξ ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 3 ∧
      Function.Surjective (SheafOfModules.sectionsMap p) ∧
      ¬ Nonempty (ShortComplex.mk i p w).Splitting := by
  obtain ⟨E, i, p, w, hS, hc, hr, hg⟩ := exists_dualSpan_extension β α s hgen ξ hξ
  refine ⟨E, i, p, w, hS, hc, hr, hg, ?_⟩
  exact not_nonempty_splitting_of_extClass_ne_zero hS (by simpa only [hc] using hne)

section Cohomology

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k))

/-- Surjectivity on actual compatible global sections implies
surjectivity on the native degree-zero derived cohomology. -/
theorem surjective_H0_of_sections_surjective {F G : X.Modules} (p : F ⟶ G)
    (hp : Function.Surjective (SheafOfModules.sectionsMap p)) :
    Function.Surjective (cohomologyOverFieldMap k f p 0) := by
  intro a
  let s := Stacks.PresheafOfModules.sectionOfTop G.val
    (cohomologyOverFieldZeroEquivSections k f G a)
  obtain ⟨t, ht⟩ := hp s
  refine ⟨(cohomologyOverFieldZeroEquivSections k f F).symm (t.eval (op ⊤)), ?_⟩
  apply (cohomologyOverFieldZeroEquivSections k f G).injective
  have htop := congrArg (fun z : G.sections => z.eval (op ⊤)) ht
  exact (cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap k f p _).trans
    ((congrArg (fun z : Γ(F, ⊤) => p.app ⊤ z)
      ((cohomologyOverFieldZeroEquivSections k f F).apply_symm_apply _)).trans
        (htop.trans (Stacks.PresheafOfModules.sectionOfTop_val_top G.val _)))

/-- Dimensions add at `H⁰` for an actual Γ-split extension. In particular,
outer dimensions three and three force the middle dimension to be six. -/
theorem finrank_H0_of_gammaSplit {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [Module.Finite k (cohomologyOverField k f S.X₁ 0)]
    [Module.Finite k (cohomologyOverField k f S.X₂ 0)]
    [Module.Finite k (cohomologyOverField k f S.X₃ 0)]
    (hgamma : Function.Surjective (SheafOfModules.sectionsMap S.g)) :
    Module.finrank k (cohomologyOverField k f S.X₂ 0) =
      Module.finrank k (cohomologyOverField k f S.X₁ 0) +
      Module.finrank k (cohomologyOverField k f S.X₃ 0) := by
  obtain ⟨δ, hinj, hex, hδ, hδ'⟩ := exists_cohomologyOverField_longExactSequence k f hS
  let u := (cohomologyOverFieldMap k f S.f 0).hom
  let v := (cohomologyOverFieldMap k f S.g 0).hom
  have hi : Function.Injective u := hinj
  have he : Function.Exact u v := hex 0
  have hs : Function.Surjective v := surjective_H0_of_sections_surjective k f S.g hgamma
  have hdim := LinearMap.finrank_range_add_finrank_ker v
  rw [LinearMap.range_eq_top.mpr hs, _root_.finrank_top, he.linearMap_ker_eq,
    LinearMap.finrank_range_of_inj hi] at hdim
  exact hdim.symm.trans (Nat.add_comm _ _)

/-- The zero space of global sections of the evaluation kernel follows
from injectivity of the actual map on `H⁰`. This is the equal-line-bundle
part of Mukai's Lemma 5.1(2), before the rank-two determinant identification. -/
theorem evaluationKernel_H0_subsingleton (β : X.Modules)
    (s : ULift.{u} (Fin 3) → β.sections) (hgen : Epi (netEvaluation β s))
    (hinj : Function.Injective (cohomologyOverFieldMap k f (netEvaluation β s) 0)) :
    Subsingleton (cohomologyOverField k f (evaluationKernel β s) 0) := by
  obtain ⟨δ, hi, he, hδ, hδ'⟩ := exists_cohomologyOverField_longExactSequence k f
    (evaluationSequence_shortExact β s hgen)
  let u := (cohomologyOverFieldMap k f (evaluationSequence β s).f 0).hom
  let v := (cohomologyOverFieldMap k f (evaluationSequence β s).g 0).hom
  have hcomp := (show Function.Exact u v from he 0).linearMap_comp_eq_zero
  have hz : ∀ a : cohomologyOverField k f (evaluationKernel β s) 0, a = 0 := by
    intro a
    apply hi
    apply hinj
    have hzv : v (u 0) = 0 := (congrArg v u.map_zero).trans v.map_zero
    exact (LinearMap.congr_fun hcomp a).trans hzv.symm
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

end Cohomology

section NativeLinearSeries

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)

/-- A basis of the actual three-dimensional section subspace of a native
degree-eight net. No completeness or basepoint-freeness is inferred. -/
def linearSeriesNetBasis (β : LinearSeries k f hdim 8 2) : Module.Basis (Fin 3) k β.V := by
  letI : Module.Finite k β.V := Module.finite_of_finrank_pos (by rw [β.finrank_eq]; decide)
  exact Module.finBasisOfFinrankEq k β.V β.finrank_eq

/-- The three actual sheaf sections obtained from the chosen native
degree-eight net, through the genuine `H⁰ ≃ Γ` comparison. -/
def linearSeriesNetSections (β : LinearSeries k f hdim 8 2) :
    ULift.{u} (Fin 3) → β.L.sections := fun i =>
  Stacks.PresheafOfModules.sectionOfTop β.L.val
    (cohomologyOverFieldZeroEquivSections k f β.L
      ((linearSeriesNetBasis k f hdim β i.down : β.V) :
        cohomologyOverField k f β.L 0))

/-- Evaluation of these sections on the top open is the literal native
cohomology-to-sections image of the net's basis. -/
theorem linearSeriesNetSections_eval_top (β : LinearSeries k f hdim 8 2)
    (i : ULift.{u} (Fin 3)) :
    (linearSeriesNetSections k f hdim β i).eval (op ⊤) =
      cohomologyOverFieldZeroEquivSections k f β.L
        ((linearSeriesNetBasis k f hdim β i.down : β.V) :
          cohomologyOverField k f β.L 0) :=
  Stacks.PresheafOfModules.sectionOfTop_val_top β.L.val _

/-- The actual dual-span bundle attached to the section subspace of a
native degree-eight net. -/
def linearSeriesDualSpan (β : LinearSeries k f hdim 8 2) : X.Modules :=
  dualSpan β.L (linearSeriesNetSections k f hdim β)

/-- Once the chosen net is proved globally generating, its constructed
dual-span bundle has rank two. -/
theorem linearSeriesDualSpan_rank (β : LinearSeries k f hdim 8 2)
    (hgen : Epi (netEvaluation β.L (linearSeriesNetSections k f hdim β))) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (linearSeriesDualSpan k f hdim β) 2 := by
  let := β.isInvertible
  exact dualSpan_rank β.L (linearSeriesNetSections k f hdim β) hgen

end NativeLinearSeries

end M9Native.MukaiBundle
