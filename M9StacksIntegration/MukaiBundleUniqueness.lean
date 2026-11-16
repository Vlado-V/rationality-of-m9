module

public import M9StacksIntegration.MukaiBundle
public import M9StacksIntegration.MukaiCohomologyParity
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Finiteness.Finsupp
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyLinear
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.FiniteLocallyFreeHomSection
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic

/-!
# Uniqueness from the actual space of Γ-split extension classes

The classes below are native `Ext¹` classes in the abelian category of sheaves
of modules.  A scalar change of an extension class is realized by a scalar
change of its injection, and the native classification of extensions then
gives an isomorphism of the actual middle sheaves.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Abelian

universe u v w t

namespace M9Native.MukaiBundleUniqueness

section LinearCategory

variable {k : Type u} [Field k] {C : Type v} [Category.{w} C] [Abelian C]
  [Linear k C] [HasExt.{t} C]

/-- The actual subspace of extension classes whose pullback by every map
from `O` vanishes.  For sheaves, `O = 𝒪_X` gives Γ-split extensions. -/
def sectionSplitSubmodule (O A B : C) : Submodule k (Ext.{t} B A 1) where
  carrier := {ξ | ∀ s : O ⟶ B, (Ext.mk₀ s).comp ξ (zero_add 1) = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy s; simp [Ext.comp_add, hx s, hy s]
  smul_mem' := by intro c x hx s; simp [hx s]

@[simp] theorem mem_sectionSplitSubmodule (O A B : C) (ξ : Ext.{t} B A 1) :
    ξ ∈ sectionSplitSubmodule (k := k) O A B ↔
      ∀ s : O ⟶ B, (Ext.mk₀ s).comp ξ (zero_add 1) = 0 := Iff.rfl

/-- Scalar multiplication by a nonzero field element is an actual
automorphism of every object of the linear category. -/
def scalarIso (A : C) (c : k) (hc : c ≠ 0) : A ≅ A where
  hom := c • 𝟙 A
  inv := c⁻¹ • 𝟙 A
  hom_inv_id := by simp [Linear.comp_smul, smul_smul, hc]
  inv_hom_id := by simp [Linear.comp_smul, smul_smul, hc]

/-- Nonzero scalar multiples of a native extension class have isomorphic
middle objects.  The isomorphism fixes the quotient; it rescales the injection. -/
theorem middle_iso_of_extClass_eq_smul
    {A B E E' : C} {i : A ⟶ E} {p : E ⟶ B} {z : i ≫ p = 0}
    {i' : A ⟶ E'} {p' : E' ⟶ B} {z' : i' ≫ p' = 0}
    (h : (ShortComplex.mk i p z).ShortExact)
    (h' : (ShortComplex.mk i' p' z').ShortExact)
    (c : k) (hc : c ≠ 0) (hclass : h'.extClass = c • h.extClass) :
    ∃ e : E ≅ E', (c⁻¹ • i) ≫ e.hom = i' ∧ e.hom ≫ p' = p := by
  let j : A ⟶ E := c⁻¹ • i
  have zj : j ≫ p = 0 := by simp [j, Linear.smul_comp, z]
  let S := ShortComplex.mk j p zj
  let e : ShortComplex.mk i p z ≅ S :=
    ShortComplex.isoMk (scalarIso A c hc) (Iso.refl E) (Iso.refl B)
      (by simp [scalarIso, S, j, Linear.smul_comp, Linear.comp_smul, smul_smul, hc])
      (by simp [S])
  have hS : S.ShortExact := ShortComplex.shortExact_of_iso e h
  have hsc : hS.extClass = c • h.extClass := by
    have hn := h.extClass_naturality hS e.hom
    change h.extClass.comp (Ext.mk₀ (c • 𝟙 A)) (add_zero 1) =
      (Ext.mk₀ (𝟙 B)).comp hS.extClass (zero_add 1) at hn
    simpa only [← Ext.smul_eq_comp_mk₀, Ext.mk₀_id_comp] using hn.symm
  have heq : hS.extClass = h'.extClass := hsc.trans hclass.symm
  exact ((Ext.extClass_surjective_and_eq_iff_iso_and_baerSum C B A).2.1
    E E' j p zj i' p' z' hS h').mp heq

/-- A finite-dimensional actual class subspace of dimension at most one
has only one isomorphism class of nontrivial middle object. -/
theorem middle_iso_of_classSubmodule_finrank_le_one
    (V : Submodule k (Ext.{t} B A 1)) [Module.Finite k V]
    (hdim : Module.finrank k V ≤ 1)
    {E E' : C} {i : A ⟶ E} {p : E ⟶ B} {z : i ≫ p = 0}
    {i' : A ⟶ E'} {p' : E' ⟶ B} {z' : i' ≫ p' = 0}
    (h : (ShortComplex.mk i p z).ShortExact)
    (h' : (ShortComplex.mk i' p' z').ShortExact)
    (hmem : h.extClass ∈ V) (hmem' : h'.extClass ∈ V)
    (hne : h.extClass ≠ 0) (hne' : h'.extClass ≠ 0) : Nonempty (E ≅ E') := by
  let x : V := ⟨h.extClass, hmem⟩
  let y : V := ⟨h'.extClass, hmem'⟩
  have hx : x ≠ 0 := by intro hx; exact hne (congrArg Subtype.val hx)
  have hy : y ≠ 0 := by intro hy; exact hne' (congrArg Subtype.val hy)
  have hpos : 0 < Module.finrank k V :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨x, hx⟩
  have hone : Module.finrank k V = 1 := by omega
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hone hx y
  have hc0 : c ≠ 0 := by intro hzero; apply hy; simpa [hzero] using hc.symm
  have hclasses : h'.extClass = c • h.extClass :=
    (congrArg Subtype.val hc).symm
  obtain ⟨e, -, -⟩ := middle_iso_of_extClass_eq_smul h h' c hc0 hclasses
  exact ⟨e⟩

/-- The actual connecting homomorphism from the kernel term of a short
exact sequence to extension classes. -/
def extensionBoundary {S : ShortComplex C} (h : S.ShortExact) (Q : C) :
    Ext.{t} S.X₁ Q 0 →ₗ[k] Ext.{t} S.X₃ Q 1 :=
  Ext.precompOfLinear h.extClass k Q (add_zero 1)

/-- The kernel is taken in the original native `Ext¹` group. -/
def extensionKernel (S : ShortComplex C) (Q : C) :
    Submodule k (Ext.{t} S.X₃ Q 1) :=
  LinearMap.ker (Ext.precompOfLinear (Ext.mk₀ S.g) k Q (zero_add 1))

theorem extensionKernel_eq_boundary_range {S : ShortComplex C}
    (h : S.ShortExact) (Q : C) :
    extensionKernel (k := k) S Q = LinearMap.range (extensionBoundary (k := k) h Q) := by
  ext ξ
  constructor
  · intro hξ
    exact Ext.contravariant_sequence_exact₃ h Q ξ hξ (add_zero 1)
  · rintro ⟨η, rfl⟩
    exact h.comp_extClass_assoc η (add_zero 1)

theorem extensionKernel_finite {S : ShortComplex C} (h : S.ShortExact) (Q : C)
    [Module.Finite k (Ext.{t} S.X₁ Q 0)] :
    Module.Finite k (extensionKernel (k := k) S Q) := by
  rw [extensionKernel_eq_boundary_range h Q]
  infer_instance

/-- The exact dimension identity computing the true extension kernel.
Vanishing of `Hom(S.X₃,Q)` makes the first restriction map injective. -/
theorem finrank_extensionKernel {S : ShortComplex C} (h : S.ShortExact) (Q : C)
    [Module.Finite k (Ext.{t} S.X₁ Q 0)]
    [Module.Finite k (Ext.{t} S.X₂ Q 0)]
    [Subsingleton (Ext.{t} S.X₃ Q 0)] :
    Module.finrank k (Ext.{t} S.X₂ Q 0) +
        Module.finrank k (extensionKernel (k := k) S Q) =
      Module.finrank k (Ext.{t} S.X₁ Q 0) := by
  let a := Ext.precompOfLinear (Ext.mk₀ S.f) k Q (zero_add 0)
  let δ := extensionBoundary (k := k) h Q
  have ha : Function.Injective a := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro ξ hξ
    obtain ⟨η, hη⟩ := Ext.contravariant_sequence_exact₂ h Q ξ hξ
    have hη0 : η = 0 := Subsingleton.elim _ _
    simpa only [hη0, Ext.comp_zero] using hη.symm
  have hex : Function.Exact a δ := by
    intro ξ
    constructor
    · intro hξ
      exact Ext.contravariant_sequence_exact₁ h Q ξ (add_zero 1) hξ
    · rintro ⟨η, rfl⟩
      exact h.extClass_comp_assoc η (h := add_zero 1)
  have hd := δ.finrank_range_add_finrank_ker
  rw [hex.linearMap_ker_eq, LinearMap.finrank_range_of_inj ha] at hd
  rw [extensionKernel_eq_boundary_range h Q]
  exact (Nat.add_comm _ _).trans hd

/-- The arithmetic in Lemma 5.4 already takes place in actual `Ext`.
The later sheaf identification of these degree-zero Ext spaces with the
specified `H⁰` spaces supplies its geometric hypotheses. -/
theorem finrank_extensionKernel_le_one {S : ShortComplex C}
    (h : S.ShortExact) (Q : C)
    [Module.Finite k (Ext.{t} S.X₁ Q 0)]
    [Module.Finite k (Ext.{t} S.X₂ Q 0)]
    [Subsingleton (Ext.{t} S.X₃ Q 0)]
    (h9 : Module.finrank k (Ext.{t} S.X₂ Q 0) = 9)
    (h10 : Module.finrank k (Ext.{t} S.X₁ Q 0) ≤ 10) :
    Module.finrank k (extensionKernel (k := k) S Q) ≤ 1 := by
  have hd := finrank_extensionKernel (k := k) h Q
  omega

/-- An even-dimensional true Hom space cannot be exhausted by the
nine-dimensional preceding Hom space, so the actual Ext kernel is nonzero. -/
theorem exists_nonzero_extensionKernel_of_even {S : ShortComplex C}
    (h : S.ShortExact) (Q : C)
    [Module.Finite k (Ext.{t} S.X₁ Q 0)]
    [Module.Finite k (Ext.{t} S.X₂ Q 0)]
    [Subsingleton (Ext.{t} S.X₃ Q 0)]
    (h9 : Module.finrank k (Ext.{t} S.X₂ Q 0) = 9)
    (heven : Even (Module.finrank k (Ext.{t} S.X₁ Q 0))) :
    ∃ ξ : Ext.{t} S.X₃ Q 1, ξ ≠ 0 ∧ ξ ∈ extensionKernel (k := k) S Q := by
  letI := extensionKernel_finite (k := k) h Q
  have hd := finrank_extensionKernel (k := k) h Q
  have hp : 0 < Module.finrank k (extensionKernel (k := k) S Q) := by
    by_contra hp
    have hz : Module.finrank k (extensionKernel (k := k) S Q) = 0 := by omega
    have hodd : Module.finrank k (Ext.{t} S.X₁ Q 0) = 9 := by omega
    rw [hodd] at heven
    norm_num at heven
  obtain ⟨ξ, hξ⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hp
  exact ⟨ξ.val, fun hz => hξ (Subtype.ext hz), ξ.property⟩

end LinearCategory

section Sheaves

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

local instance nativeHasExt : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules

/-- The actual native subspace of Γ-split extensions of `α` by `Q`. -/
def gammaSplitSubmodule (Q α : X.Modules) :
    letI := modulesLinearOverField k f
    Submodule k (Ext.{u} α Q 1) := by
  let := modulesLinearOverField k f
  exact sectionSplitSubmodule (MukaiBundle.structureModule X) Q α

@[simp] theorem mem_gammaSplitSubmodule (Q α : X.Modules) (ξ : Ext.{u} α Q 1) :
    ξ ∈ gammaSplitSubmodule k f Q α ↔
      ∀ s : MukaiBundle.structureModule X ⟶ α,
        (Ext.mk₀ s).comp ξ (zero_add 1) = 0 := Iff.rfl

/-- Membership of the actual extension class is exactly surjectivity on
the actual sheaf's compatible global sections. -/
theorem extClass_mem_gammaSplitSubmodule_iff
    {Q α E : X.Modules} {i : Q ⟶ E} {p : E ⟶ α} {z : i ≫ p = 0}
    (h : (ShortComplex.mk i p z).ShortExact) :
    h.extClass ∈ gammaSplitSubmodule k f Q α ↔
      Function.Surjective (SheafOfModules.sectionsMap p) :=
  (MukaiBundle.gammaSplit_iff_extClass_zero h).symm

/-- Pullback along the actual free evaluation map is zero for every
Γ-split class. This uses native extension realization and simultaneous
lifts of the chosen sections, not a replacement Ext group. -/
theorem evaluation_pullback_zero_of_gammaSplit
    (Q α : X.Modules) (s : ULift.{u} (Fin 3) → α.sections)
    (ξ : Ext.{u} α Q 1) (hξ : ξ ∈ gammaSplitSubmodule k f Q α) :
    (Ext.mk₀ (MukaiBundle.netEvaluation α s)).comp ξ (zero_add 1) = 0 := by
  classical
  obtain ⟨E, i, p, z, h, hc⟩ :=
    (Ext.extClass_surjective_and_eq_iff_iso_and_baerSum X.Modules α Q).1 ξ
  have hg : Function.Surjective (SheafOfModules.sectionsMap p) :=
    (MukaiBundle.gammaSplit_iff_extClass_zero h).2 (by
      rw [hc]
      exact (mem_gammaSplitSubmodule k f Q α ξ).1 hξ)
  choose t ht using fun j => hg (s j)
  have htp : E.freeHomEquiv.symm t ≫ p = MukaiBundle.netEvaluation α s := by
    apply α.freeHomEquiv.injective
    funext j
    simpa only [SheafOfModules.freeHomEquiv_comp_apply, Equiv.apply_symm_apply,
      MukaiBundle.netEvaluation] using ht j
  rw [← hc]
  exact (MukaiBundle.lifts_iff_extClass_zero h _).1 ⟨E.freeHomEquiv.symm t, htp⟩

/-- Thus the true Γ-split subspace lies in the actual Ext kernel of
the chosen dual-span evaluation sequence. Completeness is unnecessary
for this inclusion, which is all the uniqueness bound needs. -/
theorem gammaSplitSubmodule_le_evaluationKernel
    (Q α : X.Modules) (s : ULift.{u} (Fin 3) → α.sections) :
    letI := modulesLinearOverField k f
    gammaSplitSubmodule k f Q α ≤
      extensionKernel (k := k) (MukaiBundle.evaluationSequence α s) Q := by
  let := modulesLinearOverField k f
  intro ξ hξ
  exact evaluation_pullback_zero_of_gammaSplit k f Q α s ξ hξ

/-- If the three sections span all actual `Hom(𝒪_X,α)`, vanishing of
pullback along their evaluation map is exactly Γ-splitting. -/
theorem evaluationKernel_eq_gammaSplitSubmodule
    (Q α : X.Modules) (s : ULift.{u} (Fin 3) → α.sections)
    (hspan : letI := modulesLinearOverField k f
      letI := (modulesLinearOverField k f).homModule (MukaiBundle.structureModule X) α
      Submodule.span k (Set.range (fun j =>
        (α.unitHomEquiv.symm (s j) : MukaiBundle.structureModule X ⟶ α))) = ⊤) :
    letI := modulesLinearOverField k f
    extensionKernel (k := k) (MukaiBundle.evaluationSequence α s) Q =
      gammaSplitSubmodule k f Q α := by
  letI := modulesLinearOverField k f
  letI := (modulesLinearOverField k f).homModule (MukaiBundle.structureModule X) α
  apply le_antisymm
  · intro ξ hξ
    change (Ext.mk₀ (MukaiBundle.netEvaluation α s)).comp ξ (zero_add 1) = 0 at hξ
    apply (mem_gammaSplitSubmodule k f Q α ξ).2
    intro a
    have ha : a ∈ Submodule.span k (Set.range (fun j =>
        (α.unitHomEquiv.symm (s j) : MukaiBundle.structureModule X ⟶ α))) := by
      rw [hspan]
      exact Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      have hfactor : α.unitHomEquiv.symm (s j) =
          SheafOfModules.ιFree j ≫ MukaiBundle.netEvaluation α s := by
        simpa only [MukaiBundle.netEvaluation, Equiv.apply_symm_apply] using
          (SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply
            (MukaiBundle.netEvaluation α s) j)
      have hv : (Ext.mk₀ (SheafOfModules.ιFree j)).comp
          ((Ext.mk₀ (MukaiBundle.netEvaluation α s)).comp ξ (zero_add 1))
          (zero_add 1) = 0 := by rw [hξ, Ext.comp_zero]
      have hv' := (Ext.mk₀_comp_mk₀_assoc (SheafOfModules.ιFree j)
        (MukaiBundle.netEvaluation α s) ξ).symm.trans hv
      exact (congrArg (fun a : MukaiBundle.structureModule X ⟶ α =>
        (Ext.mk₀ a).comp ξ (zero_add 1)) hfactor).trans hv'
    | zero => simp
    | add a b ha hb hza hzb =>
      rw [Ext.mk₀_add, Ext.add_comp, hza, hzb, add_zero]
    | smul c a ha hza => simp [Ext.mk₀_smul, hza]
  · exact gammaSplitSubmodule_le_evaluationKernel k f Q α s

/-- Maps out of the actual free rank-three sheaf are triples of maps
out of the actual structure sheaf, by the coproduct universal property. -/
def netFreeHomEquiv (Q : X.Modules) :
    letI := modulesLinearOverField k f
    (MukaiBundle.netFree X ⟶ Q) ≃ₗ[k]
      (ULift.{u} (Fin 3) → (MukaiBundle.structureModule X ⟶ Q)) := by
  letI := modulesLinearOverField k f
  refine
    { toFun := fun g j => SheafOfModules.ιFree j ≫ g
      invFun := fun v => Sigma.desc v
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_smul' := ?_ }
  · intro g h
    funext j
    simp only [Pi.add_apply, Preadditive.comp_add]
  · intro c g
    funext j
    simp only [Pi.smul_apply, RingHom.id_apply, Linear.comp_smul]
  · intro g
    apply Sigma.hom_ext
    intro j
    simp [SheafOfModules.ιFree]
  · intro v
    funext j
    simp [SheafOfModules.ιFree]

/-- The native degree-zero Ext space from `𝒪_X³` is the actual triple
of `H⁰(Q)`, with its canonical base-field scalar action. -/
def netFreeExtZeroEquiv (Q : X.Modules) :
    letI := modulesLinearOverField k f
    Ext.{u} (MukaiBundle.netFree X) Q 0 ≃ₗ[k]
      (ULift.{u} (Fin 3) → cohomologyOverField k f Q 0) := by
  letI := modulesLinearOverField k f
  exact (Ext.linearEquiv₀ (R := k)).trans ((netFreeHomEquiv k f Q).trans
    (LinearEquiv.piCongrRight fun _ => unitHomLinearEquivCohomologyZero k f Q))

theorem finrank_netFreeExtZero (Q : X.Modules)
    [Module.Finite k (cohomologyOverField k f Q 0)] :
    letI := modulesLinearOverField k f
    Module.finrank k (Ext.{u} (MukaiBundle.netFree X) Q 0) =
      3 * Module.finrank k (cohomologyOverField k f Q 0) := by
  letI := modulesLinearOverField k f
  rw [(netFreeExtZeroEquiv k f Q).finrank_eq, Module.finrank_pi_fintype]
  simp

/-- The actual sheaf-Hom global-section comparison is linear over the
original base field, not only an additive equivalence. -/
def homH0SheafHomLinearEquiv (E Q : X.Modules) :
    letI := modulesLinearOverField k f
    (E ⟶ Q) ≃ₗ[k]
      cohomologyOverField k f ((Stacks.Algebraization.sheafHomFunctor X E).obj Q) 0 := by
  letI := modulesLinearOverField k f
  let H := (Stacks.Algebraization.sheafHomFunctor X E).obj Q
  let e := Stacks.Algebraization.internalHomSectionsTopMapAddEquiv E Q
  let z := cohomologyOverFieldZeroIsoSections k f H
  refine
    { toAddEquiv := e.trans z.toLinearEquiv.toAddEquiv.symm
      map_smul' := ?_ }
  intro c g
  apply z.toLinearEquiv.injective
  change z.toLinearEquiv (z.toLinearEquiv.symm (e (c • g))) =
    z.toLinearEquiv (c • z.toLinearEquiv.symm (e g))
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.map_smul, LinearEquiv.apply_symm_apply]
  change e (c • g) = ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom c • e g
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext x
  have hr := Stacks.SheafOfModules.internalHom_smul_app_apply X.sheaf.obj E.val Q.val
    (⊤ : X.Opens) (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom c) (e g) U x
  apply Eq.trans ?_ hr.symm
  change (g.val.app (op U.unop.left))
      (baseRingToSections k (Over.mk f) (op U.unop.left) c • x) = _
  rw [(g.val.app (op U.unop.left)).hom.map_smul]
  rfl

/-- Native degree-zero Ext from a finite locally free sheaf is `H⁰`
of the actual tensor product with its actual dual. -/
def extZeroTensorDualEquiv (E Q : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    letI := modulesLinearOverField k f
    Ext.{u} E Q 0 ≃ₗ[k]
      cohomologyOverField k f
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj Q).obj
          (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf E)) 0 := by
  letI := modulesLinearOverField k f
  exact (Ext.linearEquiv₀ (R := k)).trans ((homH0SheafHomLinearEquiv k f E Q).trans
    (cohomologyOverFieldIso k f
      (Stacks.SheafOfModules.tensorDualIsoSheafHomOfRank E Q r).symm 0).toLinearEquiv)

/-- The genuine Γ-split extension class lies in a kernel of dimension
at most one whenever the actual degree-zero Ext dimensions are `9` and
at most `10`. This does not assume the desired uniqueness conclusion. -/
theorem gammaSplit_middle_iso_of_evaluation_dimensions
    {Q α E E' : X.Modules} (s : ULift.{u} (Fin 3) → α.sections)
    (hs : Epi (MukaiBundle.netEvaluation α s))
    [Module.Finite k (cohomologyOverField k f Q 0)]
    (hQ : Module.finrank k (cohomologyOverField k f Q 0) = 3)
    (hfinite : letI := modulesLinearOverField k f
      Module.Finite k (Ext.{u} (MukaiBundle.evaluationKernel α s) Q 0))
    (hvan : letI := modulesLinearOverField k f
      Subsingleton (Ext.{u} α Q 0))
    (h10 : letI := modulesLinearOverField k f
      Module.finrank k (Ext.{u} (MukaiBundle.evaluationKernel α s) Q 0) ≤ 10)
    {i : Q ⟶ E} {p : E ⟶ α} {z : i ≫ p = 0}
    {i' : Q ⟶ E'} {p' : E' ⟶ α} {z' : i' ≫ p' = 0}
    (h : (ShortComplex.mk i p z).ShortExact)
    (h' : (ShortComplex.mk i' p' z').ShortExact)
    (hg : Function.Surjective (SheafOfModules.sectionsMap p))
    (hg' : Function.Surjective (SheafOfModules.sectionsMap p'))
    (hn : ¬ Nonempty (ShortComplex.mk i p z).Splitting)
    (hn' : ¬ Nonempty (ShortComplex.mk i' p' z').Splitting) : Nonempty (E ≅ E') := by
  letI := modulesLinearOverField k f
  letI := hfinite
  letI := hvan
  letI : Module.Finite k (Ext.{u} (MukaiBundle.netFree X) Q 0) :=
    Module.Finite.equiv (netFreeExtZeroEquiv k f Q).symm
  let S := MukaiBundle.evaluationSequence α s
  let V : Submodule k (Ext.{u} α Q 1) :=
    extensionKernel (k := k) (MukaiBundle.evaluationSequence α s) Q
  have hS := MukaiBundle.evaluationSequence_shortExact α s hs
  letI : Module.Finite k (Ext.{u} S.X₁ Q 0) := hfinite
  letI : Module.Finite k (Ext.{u} S.X₂ Q 0) :=
    Module.Finite.equiv (netFreeExtZeroEquiv k f Q).symm
  letI : Subsingleton (Ext.{u} S.X₃ Q 0) := hvan
  letI : Module.Finite k V := extensionKernel_finite hS Q
  have hle : gammaSplitSubmodule k f Q α ≤ V :=
    gammaSplitSubmodule_le_evaluationKernel k f Q α s
  letI : Module.Finite k (gammaSplitSubmodule k f Q α) :=
    Submodule.finiteDimensional_of_le hle
  apply middle_iso_of_classSubmodule_finrank_le_one (gammaSplitSubmodule k f Q α) _ h h'
    ((extClass_mem_gammaSplitSubmodule_iff k f h).2 hg)
    ((extClass_mem_gammaSplitSubmodule_iff k f h').2 hg')
    (fun hz => hn (by
      obtain ⟨t, ht⟩ := (MukaiBundle.lifts_iff_extClass_zero h (𝟙 α)).2 (by simp [hz])
      exact ⟨ShortComplex.Splitting.ofExactOfSection _ h.exact t ht h.mono_f⟩))
    (fun hz => hn' (by
      obtain ⟨t, ht⟩ := (MukaiBundle.lifts_iff_extClass_zero h' (𝟙 α)).2 (by simp [hz])
      exact ⟨ShortComplex.Splitting.ofExactOfSection _ h'.exact t ht h'.mono_f⟩))
  exact (Submodule.finrank_mono hle).trans
    (finrank_extensionKernel_le_one hS Q (by
      change Module.finrank k (Ext.{u} (MukaiBundle.netFree X) Q 0) = 9
      rw [finrank_netFreeExtZero k f Q, hQ]) h10)

/-- The actual dual-span specialization of the preceding Ext computation.
The remaining geometric hypothesis is the `H⁰(Qβ ⊗ Qα)` bound, not an
assumed one-dimensional Ext space or a uniqueness predicate. -/
theorem gammaSplit_middle_iso_of_tensor_H0_bound
    {Q α E E' : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 α]
    (s : ULift.{u} (Fin 3) → α.sections)
    (hs : Epi (MukaiBundle.netEvaluation α s))
    [Module.Finite k (cohomologyOverField k f Q 0)]
    [Module.Finite k (cohomologyOverField k f
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj Q).obj
        (MukaiBundle.dualSpan α s)) 0)]
    (hQ : Module.finrank k (cohomologyOverField k f Q 0) = 3)
    (hvan : Subsingleton (α ⟶ Q))
    (h10 : Module.finrank k (cohomologyOverField k f
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj Q).obj
        (MukaiBundle.dualSpan α s)) 0) ≤ 10)
    {i : Q ⟶ E} {p : E ⟶ α} {z : i ≫ p = 0}
    {i' : Q ⟶ E'} {p' : E' ⟶ α} {z' : i' ≫ p' = 0}
    (h : (ShortComplex.mk i p z).ShortExact)
    (h' : (ShortComplex.mk i' p' z').ShortExact)
    (hg : Function.Surjective (SheafOfModules.sectionsMap p))
    (hg' : Function.Surjective (SheafOfModules.sectionsMap p'))
    (hn : ¬ Nonempty (ShortComplex.mk i p z).Splitting)
    (hn' : ¬ Nonempty (ShortComplex.mk i' p' z').Splitting) : Nonempty (E ≅ E') := by
  letI := modulesLinearOverField k f
  letI := hvan
  have hvanExt : Subsingleton (Ext.{u} α Q 0) := (Ext.addEquiv₀.toEquiv).subsingleton
  letI := MukaiBundle.evaluationKernel_rank α s hs
  letI : Module.Finite k (cohomologyOverField k f
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj Q).obj
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
          (MukaiBundle.evaluationKernel α s))) 0) :=
    inferInstanceAs (Module.Finite k (cohomologyOverField k f
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj Q).obj
        (MukaiBundle.dualSpan α s)) 0))
  let e := extZeroTensorDualEquiv k f (MukaiBundle.evaluationKernel α s) Q 2
  have hfinite : Module.Finite k (Ext.{u} (MukaiBundle.evaluationKernel α s) Q 0) :=
    Module.Finite.equiv e.symm
  apply gammaSplit_middle_iso_of_evaluation_dimensions k f s hs hQ hfinite hvanExt
    _ h h' hg hg' hn hn'
  exact e.finrank_eq.trans_le h10

/-- The true Ext construction of Mukai Lemma 5.2, conditional only on
the stated geometric vanishing and parity of the actual tensor bundle.
The nonzero class and its actual nonsplit middle sheaf are produced here. -/
theorem exists_nonsplit_gammaSplit_of_even_tensor_H0
    (Q α : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 α]
    (hQrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Q 2)
    (s : ULift.{u} (Fin 3) → α.sections)
    (hs : Epi (MukaiBundle.netEvaluation α s))
    [Module.Finite k (cohomologyOverField k f Q 0)]
    [Module.Finite k (cohomologyOverField k f
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj Q).obj
        (MukaiBundle.dualSpan α s)) 0)]
    (hQ : Module.finrank k (cohomologyOverField k f Q 0) = 3)
    (hvan : Subsingleton (α ⟶ Q))
    (hspan : letI := modulesLinearOverField k f
      letI := (modulesLinearOverField k f).homModule (MukaiBundle.structureModule X) α
      Submodule.span k (Set.range (fun j =>
        (α.unitHomEquiv.symm (s j) : MukaiBundle.structureModule X ⟶ α))) = ⊤)
    (heven : Even (Module.finrank k (cohomologyOverField k f
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj Q).obj
        (MukaiBundle.dualSpan α s)) 0))) :
    ∃ (E : X.Modules) (i : Q ⟶ E) (p : E ⟶ α) (z : i ≫ p = 0)
      (h : (ShortComplex.mk i p z).ShortExact),
      h.extClass ≠ 0 ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 3 ∧
      Function.Surjective (SheafOfModules.sectionsMap p) ∧
      ¬ Nonempty (ShortComplex.mk i p z).Splitting := by
  letI := modulesLinearOverField k f
  letI := hvan
  letI : Subsingleton (Ext.{u} α Q 0) := (Ext.addEquiv₀.toEquiv).subsingleton
  letI := MukaiBundle.evaluationKernel_rank α s hs
  let T := (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj Q).obj
    (MukaiBundle.dualSpan α s))
  letI : Module.Finite k (cohomologyOverField k f
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj Q).obj
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
          (MukaiBundle.evaluationKernel α s))) 0) :=
    inferInstanceAs (Module.Finite k (cohomologyOverField k f T 0))
  let e := extZeroTensorDualEquiv k f (MukaiBundle.evaluationKernel α s) Q 2
  letI : Module.Finite k (Ext.{u} (MukaiBundle.evaluationKernel α s) Q 0) :=
    Module.Finite.equiv e.symm
  letI : Module.Finite k (Ext.{u} (MukaiBundle.netFree X) Q 0) :=
    Module.Finite.equiv (netFreeExtZeroEquiv k f Q).symm
  let S := MukaiBundle.evaluationSequence α s
  have hS := MukaiBundle.evaluationSequence_shortExact α s hs
  letI : Module.Finite k (Ext.{u} S.X₁ Q 0) :=
    Module.Finite.equiv e.symm
  letI : Module.Finite k (Ext.{u} S.X₂ Q 0) :=
    Module.Finite.equiv (netFreeExtZeroEquiv k f Q).symm
  letI : Subsingleton (S.X₃ ⟶ Q) := hvan
  letI : Subsingleton (Ext.{u} S.X₃ Q 0) := (Ext.addEquiv₀.toEquiv).subsingleton
  obtain ⟨ξ, hξ, hmem⟩ := exists_nonzero_extensionKernel_of_even (k := k) hS Q
    (by change Module.finrank k (Ext.{u} (MukaiBundle.netFree X) Q 0) = 9
        rw [finrank_netFreeExtZero k f Q, hQ])
    (by change Even (Module.finrank k (Ext.{u} (MukaiBundle.evaluationKernel α s) Q 0))
        rw [e.finrank_eq]
        exact heven)
  have hg : ξ ∈ gammaSplitSubmodule k f Q α := by
    rw [← evaluationKernel_eq_gammaSplitSubmodule k f Q α s hspan]
    exact hmem
  obtain ⟨E, i, p, z, h, hc, hr, hγ⟩ := MukaiBundle.exists_rankThree_gammaSplit_extension
    Q α hQrank (SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X α) ξ
    ((mem_gammaSplitSubmodule k f Q α ξ).1 hg)
  refine ⟨E, i, p, z, h, ?_, hr, hγ, ?_⟩
  · simpa only [hc] using hξ
  · exact MukaiBundle.not_nonempty_splitting_of_extClass_ne_zero h (by simpa only [hc] using hξ)

/-- A short exact sequence of actual sheaves splits precisely when its
native class vanishes. -/
theorem extClass_eq_zero_iff_splitting {S : ShortComplex X.Modules}
    (h : S.ShortExact) : h.extClass = 0 ↔ Nonempty S.Splitting := by
  constructor
  · intro hz
    obtain ⟨s, hs⟩ := (MukaiBundle.lifts_iff_extClass_zero h (𝟙 S.X₃)).2
      (by simp [hz])
    exact ⟨ShortComplex.Splitting.ofExactOfSection S h.exact s hs h.mono_f⟩
  · rintro ⟨s⟩
    have hz := (MukaiBundle.lifts_iff_extClass_zero h (𝟙 S.X₃)).1 ⟨s.s, s.s_g⟩
    simpa using hz

/-- Surjectivity on the native derived `H⁰` is also surjectivity on
the original sheaf's compatible global sections. -/
theorem sections_surjective_of_H0_surjective {E G : X.Modules} (p : E ⟶ G)
    (hp : Function.Surjective (cohomologyOverFieldMap k f p 0)) :
    Function.Surjective (SheafOfModules.sectionsMap p) := by
  intro s
  let a := (cohomologyOverFieldZeroEquivSections k f G).symm (s.eval (op ⊤))
  obtain ⟨b, hb⟩ := hp a
  let t := Stacks.PresheafOfModules.sectionOfTop E.val
    (cohomologyOverFieldZeroEquivSections k f E b)
  refine ⟨t, ?_⟩
  apply (bijective_sections_eval_top G).injective
  change p.app ⊤ (t.eval (op ⊤)) = s.eval (op ⊤)
  have ht : t.eval (op ⊤) = cohomologyOverFieldZeroEquivSections k f E b :=
    Stacks.PresheafOfModules.sectionOfTop_val_top E.val _
  exact (congrArg (fun y => p.app ⊤ y) ht).trans
    ((cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap k f p b).symm.trans
    ((congrArg (cohomologyOverFieldZeroEquivSections k f G) hb).trans
      ((cohomologyOverFieldZeroEquivSections k f G).apply_symm_apply _)))

/-- If dimensions add in degree zero, exactness forces Γ-splitting.
No surjectivity of the section map is assumed. -/
theorem gammaSplit_of_finrank_H0_eq {S : ShortComplex X.Modules} (h : S.ShortExact)
    [Module.Finite k (cohomologyOverField k f S.X₁ 0)]
    [Module.Finite k (cohomologyOverField k f S.X₂ 0)]
    [Module.Finite k (cohomologyOverField k f S.X₃ 0)]
    (hdim : Module.finrank k (cohomologyOverField k f S.X₂ 0) =
      Module.finrank k (cohomologyOverField k f S.X₁ 0) +
        Module.finrank k (cohomologyOverField k f S.X₃ 0)) :
    Function.Surjective (SheafOfModules.sectionsMap S.g) := by
  apply sections_surjective_of_H0_surjective k f S.g
  let u := (cohomologyOverFieldMap k f S.f 0).hom
  let v := (cohomologyOverFieldMap k f S.g 0).hom
  have hu : Function.Injective u :=
    MukaiCohomologyParity.cohomologyBoundary_injective_left k f h
  have hex : Function.Exact u v :=
    MukaiCohomologyParity.cohomologyBoundary_exact_left k f h 0
  have hrank := v.finrank_range_add_finrank_ker
  rw [hex.linearMap_ker_eq, LinearMap.finrank_range_of_inj hu] at hrank
  change Function.Surjective v
  exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq (by omega))

/-- The section count in Mukai's Lemma 5.4 is exactly Γ-splitting when
both actual end sheaves have three independent sections. -/
theorem gammaSplit_iff_H0_six {S : ShortComplex X.Modules} (h : S.ShortExact)
    [Module.Finite k (cohomologyOverField k f S.X₁ 0)]
    [Module.Finite k (cohomologyOverField k f S.X₂ 0)]
    [Module.Finite k (cohomologyOverField k f S.X₃ 0)]
    (h1 : Module.finrank k (cohomologyOverField k f S.X₁ 0) = 3)
    (h3 : Module.finrank k (cohomologyOverField k f S.X₃ 0) = 3) :
    Function.Surjective (SheafOfModules.sectionsMap S.g) ↔
      Module.finrank k (cohomologyOverField k f S.X₂ 0) = 6 := by
  constructor
  · intro hg
    simpa only [h1, h3] using MukaiBundle.finrank_H0_of_gammaSplit k f h hg
  · intro hd
    apply gammaSplit_of_finrank_H0_eq k f h
    simp only [h1, h3, hd]

/-- `H⁰` of a Γ-split extension is finite as soon as the two endpoint
spaces are finite. This derives finiteness for the constructed middle sheaf. -/
theorem finite_H0_of_gammaSplit {S : ShortComplex X.Modules} (h : S.ShortExact)
    [Module.Finite k (cohomologyOverField k f S.X₁ 0)]
    [Module.Finite k (cohomologyOverField k f S.X₃ 0)]
    (hg : Function.Surjective (SheafOfModules.sectionsMap S.g)) :
    Module.Finite k (cohomologyOverField k f S.X₂ 0) :=
  Module.Finite.of_exact
    (MukaiCohomologyParity.cohomologyBoundary_exact_left k f h 0)
    (MukaiBundle.surjective_H0_of_sections_surjective k f S.g hg)

/-- The actual extension produced by the parity argument has six
sections when both of its actual endpoint sheaves have three sections. -/
theorem exists_nonsplit_H0_six_of_even_tensor_H0
    (Q α : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 α]
    (hQrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Q 2)
    (s : ULift.{u} (Fin 3) → α.sections)
    (hs : Epi (MukaiBundle.netEvaluation α s))
    [Module.Finite k (cohomologyOverField k f Q 0)]
    [Module.Finite k (cohomologyOverField k f α 0)]
    [Module.Finite k (cohomologyOverField k f
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj Q).obj
        (MukaiBundle.dualSpan α s)) 0)]
    (hQ : Module.finrank k (cohomologyOverField k f Q 0) = 3)
    (hα : Module.finrank k (cohomologyOverField k f α 0) = 3)
    (hvan : Subsingleton (α ⟶ Q))
    (hspan : letI := modulesLinearOverField k f
      letI := (modulesLinearOverField k f).homModule (MukaiBundle.structureModule X) α
      Submodule.span k (Set.range (fun j =>
        (α.unitHomEquiv.symm (s j) : MukaiBundle.structureModule X ⟶ α))) = ⊤)
    (heven : Even (Module.finrank k (cohomologyOverField k f
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj Q).obj
        (MukaiBundle.dualSpan α s)) 0))) :
    ∃ (E : X.Modules) (i : Q ⟶ E) (p : E ⟶ α) (z : i ≫ p = 0)
      (h : (ShortComplex.mk i p z).ShortExact),
      h.extClass ≠ 0 ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 3 ∧
      Function.Surjective (SheafOfModules.sectionsMap p) ∧
      ¬ Nonempty (ShortComplex.mk i p z).Splitting ∧
      Module.finrank k (cohomologyOverField k f E 0) = 6 := by
  obtain ⟨E, i, p, z, h, hc, hr, hg, hn⟩ :=
    exists_nonsplit_gammaSplit_of_even_tensor_H0 k f Q α hQrank s hs hQ hvan hspan heven
  letI : Module.Finite k (cohomologyOverField k f E 0) := finite_H0_of_gammaSplit k f h hg
  refine ⟨E, i, p, z, h, hc, hr, hg, hn, ?_⟩
  exact (gammaSplit_iff_H0_six k f h hQ hα).1 hg

/-- One-dimensionality of the actual Γ-split Ext subspace classifies all
nonsplit Γ-split extensions, by isomorphisms of their middle sheaves. -/
theorem gammaSplit_middle_iso
    {Q α E E' : X.Modules}
    [Module.Finite k (gammaSplitSubmodule k f Q α)]
    (hdim : Module.finrank k (gammaSplitSubmodule k f Q α) ≤ 1)
    {i : Q ⟶ E} {p : E ⟶ α} {z : i ≫ p = 0}
    {i' : Q ⟶ E'} {p' : E' ⟶ α} {z' : i' ≫ p' = 0}
    (h : (ShortComplex.mk i p z).ShortExact)
    (h' : (ShortComplex.mk i' p' z').ShortExact)
    (hg : Function.Surjective (SheafOfModules.sectionsMap p))
    (hg' : Function.Surjective (SheafOfModules.sectionsMap p'))
    (hn : ¬ Nonempty (ShortComplex.mk i p z).Splitting)
    (hn' : ¬ Nonempty (ShortComplex.mk i' p' z').Splitting) : Nonempty (E ≅ E') := by
  let := modulesLinearOverField k f
  exact middle_iso_of_classSubmodule_finrank_le_one (gammaSplitSubmodule k f Q α) hdim
    h h' ((extClass_mem_gammaSplitSubmodule_iff k f h).2 hg)
    ((extClass_mem_gammaSplitSubmodule_iff k f h').2 hg')
    (fun hz => hn ((extClass_eq_zero_iff_splitting h).1 hz))
    (fun hz => hn' ((extClass_eq_zero_iff_splitting h').1 hz))

/-- The actual kernel at `H¹(S.X₁)` in the native cohomology sequence. -/
def cohomologyKernel {S : ShortComplex X.Modules} (_h : S.ShortExact) :
    Submodule k (cohomologyOverField k f S.X₁ 1) :=
  LinearMap.ker (cohomologyOverFieldMap k f S.f 1).hom

theorem cohomologyKernel_eq_boundary_range {S : ShortComplex X.Modules}
    (h : S.ShortExact) :
    cohomologyKernel k f h =
      LinearMap.range (MukaiCohomologyParity.cohomologyBoundary k f h 0).hom :=
  (MukaiCohomologyParity.cohomologyBoundary_exact_right k f h 0).linearMap_ker_eq

/-- Finiteness of the actual kernel follows from the preceding `H⁰`,
without assuming that the entire `H¹` group is finite. -/
instance cohomologyKernel_finite {S : ShortComplex X.Modules} (h : S.ShortExact)
    [Module.Finite k (cohomologyOverField k f S.X₃ 0)] :
    Module.Finite k (cohomologyKernel k f h) := by
  rw [cohomologyKernel_eq_boundary_range k f h]
  infer_instance

/-- The exact-sequence step in Mukai's Lemma 5.4: the actual `H⁰` bound
`h⁰(Qα ⊗ Qβ) ≤ 10` bounds the relevant actual `H¹` kernel by one, once the
preceding space has dimension nine and the first `H⁰` vanishes. -/
theorem finrank_cohomologyKernel_le_one {S : ShortComplex X.Modules}
    (h : S.ShortExact)
    [Subsingleton (cohomologyOverField k f S.X₁ 0)]
    [Module.Finite k (cohomologyOverField k f S.X₂ 0)]
    [Module.Finite k (cohomologyOverField k f S.X₃ 0)]
    (h9 : Module.finrank k (cohomologyOverField k f S.X₂ 0) = 9)
    (h10 : Module.finrank k (cohomologyOverField k f S.X₃ 0) ≤ 10) :
    Module.finrank k (cohomologyKernel k f h) ≤ 1 := by
  have hh := MukaiCohomologyParity.finrank_H0_add_boundary_range k f h
  have hz : Module.finrank k (cohomologyOverField k f S.X₁ 0) = 0 :=
    Module.finrank_zero_of_subsingleton
  have he : Module.finrank k (cohomologyKernel k f h) =
      Module.finrank k
        (LinearMap.range (MukaiCohomologyParity.cohomologyBoundary k f h 0).hom) := by
    rw [cohomologyKernel_eq_boundary_range k f h]
  omega

/-- The degree-zero dimension inequality of an actual short exact
sequence, without assuming surjectivity of the last `H⁰` map. -/
theorem finrank_H0_le_add {S : ShortComplex X.Modules} (h : S.ShortExact)
    [Module.Finite k (cohomologyOverField k f S.X₁ 0)]
    [Module.Finite k (cohomologyOverField k f S.X₂ 0)]
    [Module.Finite k (cohomologyOverField k f S.X₃ 0)] :
    Module.finrank k (cohomologyOverField k f S.X₂ 0) ≤
      Module.finrank k (cohomologyOverField k f S.X₁ 0) +
        Module.finrank k (cohomologyOverField k f S.X₃ 0) := by
  have he := MukaiCohomologyParity.finrank_H0_add_boundary_range k f h
  omega

/-- The exact arithmetic used after tensoring Mukai's sequence (5.2).
The Serre-dual endpoint has the same `H⁰` as `H¹` of the first bundle,
whose Euler characteristic is `−4`; an actual `H⁰ ≤ 3` bound therefore
gives the required actual `H⁰ ≤ 10` bound for the middle tensor bundle. -/
theorem tensor_H0_le_ten_of_twist_H0_le_three
    {S : ShortComplex X.Modules} (h : S.ShortExact)
    [Module.Finite k (cohomologyOverField k f S.X₁ 0)]
    [Module.Finite k (cohomologyOverField k f S.X₂ 0)]
    [Module.Finite k (cohomologyOverField k f S.X₃ 0)]
    (hSerre : Module.finrank k (cohomologyOverField k f S.X₃ 0) =
      Module.finrank k (cohomologyOverField k f S.X₁ 1))
    (hEuler : (Module.finrank k (cohomologyOverField k f S.X₁ 0) : ℤ) -
      Module.finrank k (cohomologyOverField k f S.X₁ 1) = -4)
    (h3 : Module.finrank k (cohomologyOverField k f S.X₁ 0) ≤ 3) :
    Module.finrank k (cohomologyOverField k f S.X₂ 0) ≤ 10 := by
  have he := finrank_H0_le_add k f h
  omega

/-- The precise bridge consumed by the geometric Ext/cohomology
identification: an actual linear equivalence to the actual `H¹` kernel
transports the bound and yields isomorphism of the middle sheaves. -/
theorem gammaSplit_middle_iso_of_cohomologyKernel
    {Q α E E' : X.Modules} {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [Subsingleton (cohomologyOverField k f S.X₁ 0)]
    [Module.Finite k (cohomologyOverField k f S.X₂ 0)]
    [Module.Finite k (cohomologyOverField k f S.X₃ 0)]
    (e : gammaSplitSubmodule k f Q α ≃ₗ[k] cohomologyKernel k f hS)
    (h9 : Module.finrank k (cohomologyOverField k f S.X₂ 0) = 9)
    (h10 : Module.finrank k (cohomologyOverField k f S.X₃ 0) ≤ 10)
    {i : Q ⟶ E} {p : E ⟶ α} {z : i ≫ p = 0}
    {i' : Q ⟶ E'} {p' : E' ⟶ α} {z' : i' ≫ p' = 0}
    (h : (ShortComplex.mk i p z).ShortExact)
    (h' : (ShortComplex.mk i' p' z').ShortExact)
    (hg : Function.Surjective (SheafOfModules.sectionsMap p))
    (hg' : Function.Surjective (SheafOfModules.sectionsMap p'))
    (hn : ¬ Nonempty (ShortComplex.mk i p z).Splitting)
    (hn' : ¬ Nonempty (ShortComplex.mk i' p' z').Splitting) : Nonempty (E ≅ E') := by
  let : Module.Finite k (gammaSplitSubmodule k f Q α) := Module.Finite.equiv e.symm
  apply gammaSplit_middle_iso k f (h := h) (h' := h') _ hg hg' hn hn'
  rw [e.finrank_eq]
  exact finrank_cohomologyKernel_le_one k f hS h9 h10

end Sheaves

end M9Native.MukaiBundleUniqueness
