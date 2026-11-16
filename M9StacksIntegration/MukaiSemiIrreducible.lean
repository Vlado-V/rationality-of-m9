module

public import M9StacksIntegration.MukaiBundle
public import M9StacksIntegration.MukaiRankTwoCriterion
public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatShortExactSequence
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Native evaluation maps for Mukai's semi-irreducible linear systems

All bundles in this file are actual objects of `X.Modules`. Sections are
the native `cohomologyOverField` in degree zero. Evaluation is the morphism
of sheaves determined by those sections, and the rank of a morphism at a
point is the rank of its residue-field linear map, not the fibre rank of
its sheaf-theoretic image. These differ when the image is not saturated.

Mukai Definition 3.3 is expressed using every independent `r`-tuple of
sections. Such a tuple is precisely a choice of basis for an
`r`-dimensional section subspace. Thus its evaluation source is the
corresponding actual free sheaf `O_X^r`. The complete-system definition
uses the whole native space of sections, with no semi-irreducibility
assumption attached to the construction of a bundle.

The original statements are in Mukai, *Curves and symmetric spaces II*,
Definition 3.3 and Propositions 3.2 and 5.3. The status of the latter two
geometric proofs is recorded separately in the accompanying audit.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Preadditive
open scoped TensorProduct

universe u

namespace M9Native.MukaiSemiIrreducible

variable {X : Scheme.{u}}

/-- The actual residue-field fibre `κ(x) ⊗_{O_x} F_x`. -/
abbrev Fiber (F : X.Modules) (x : X) : Type u :=
  letI := Stacks.SheafOfModules.FlatShortExact.stalkModule
    (X := X.toRingedSpace) F x
  letI : Algebra (X.presheaf.stalk x) (X.residueField x) :=
    (X.residue x).hom.toAlgebra
  X.residueField x ⊗[X.presheaf.stalk x] (F.presheaf.stalk x)

/-- A morphism of actual sheaves induces its original residue-field
linear map on fibres. Tensoring is performed after taking the actual
stalk map. -/
def fiberMap {F G : X.Modules} (φ : F ⟶ G) (x : X) :
    letI := Stacks.SheafOfModules.FlatShortExact.stalkModule
      (X := X.toRingedSpace) F x
    letI := Stacks.SheafOfModules.FlatShortExact.stalkModule
      (X := X.toRingedSpace) G x
    letI : Algebra (X.presheaf.stalk x) (X.residueField x) :=
      (X.residue x).hom.toAlgebra
    Fiber F x →ₗ[X.residueField x] Fiber G x :=
  letI := Stacks.SheafOfModules.FlatShortExact.stalkModule
    (X := X.toRingedSpace) F x
  letI := Stacks.SheafOfModules.FlatShortExact.stalkModule
    (X := X.toRingedSpace) G x
  letI : Algebra (X.presheaf.stalk x) (X.residueField x) :=
    (X.residue x).hom.toAlgebra
  (Stacks.SheafOfModules.FlatShortExact.stalkLinearMap
    (X := X.toRingedSpace) φ x).baseChange (X.residueField x)

/-- Rank of the actual fibre linear map at one point. Taking an image
before passing to the fibre would give an incorrect definition here. -/
def mapRankAt {F G : X.Modules} (φ : F ⟶ G) (x : X) : ℕ :=
  letI := Stacks.SheafOfModules.FlatShortExact.stalkModule
    (X := X.toRingedSpace) F x
  letI := Stacks.SheafOfModules.FlatShortExact.stalkModule
    (X := X.toRingedSpace) G x
  letI : Algebra (X.presheaf.stalk x) (X.residueField x) :=
    (X.residue x).hom.toAlgebra
  Module.finrank (X.residueField x) (LinearMap.range (fiberMap φ x))

/-- A sheaf morphism has rank `r` on every residue-field fibre. -/
def EverywhereRank {F G : X.Modules} (φ : F ⟶ G) (r : ℕ) : Prop :=
  ∀ x : X, mapRankAt φ x = r

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k))

/-- Send an original native zeroth-cohomology class to its compatible
family of sheaf sections using the canonical comparison. -/
def sectionOfH0 (E : X.Modules) (s : cohomologyOverField k f E 0) : E.sections :=
  Stacks.PresheafOfModules.sectionOfTop E.val
    ((cohomologyOverFieldZeroLinearIso k f E).hom s)

@[simp] theorem sectionOfH0_eval_top (E : X.Modules)
    (s : cohomologyOverField k f E 0) :
    (sectionOfH0 k f E s).eval (op ⊤) =
      (cohomologyOverFieldZeroLinearIso k f E).hom s :=
  Stacks.PresheafOfModules.sectionOfTop_val_top E.val _

/-- The actual evaluation map of a finite tuple of native sections. -/
def evaluation {r : ℕ} (E : X.Modules)
    (s : Fin r → cohomologyOverField k f E 0) :
    _root_.SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)) ⟶ E :=
  E.freeHomEquiv.symm (fun i => sectionOfH0 k f E (s i.down))

/-- The evaluation map has the prescribed native section on each free
generator; this is the actual sheaf map, not a rank surrogate. -/
theorem evaluation_freeSection {r : ℕ} (E : X.Modules)
    (s : Fin r → cohomologyOverField k f E 0) (i : ULift.{u} (Fin r)) :
    _root_.SheafOfModules.sectionsMap (evaluation k f E s)
      (_root_.SheafOfModules.freeSection i) = sectionOfH0 k f E (s i.down) :=
  _root_.SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection _ i

/-- Semi-irreducibility for an actual section subspace, in basis form.
The alternatives are sheaf monicity and rank `r-1` at **every** point. -/
def SemiIrreducible (E : X.Modules) (r : ℕ)
    (A : Submodule k (cohomologyOverField k f E 0)) : Prop :=
  ∀ s : Fin r → A, LinearIndependent k s →
    Mono (evaluation k f E (fun i => (s i : cohomologyOverField k f E 0))) ∨
      EverywhereRank (evaluation k f E (fun i => (s i : cohomologyOverField k f E 0))) (r - 1)

/-- Mukai Definition 3.3 for the complete linear system of an actual
bundle: every independent tuple in the whole native section space is
tested. Rank and finite local freeness remain separate bundle hypotheses. -/
def CompleteSemiIrreducible (E : X.Modules) (r : ℕ) : Prop :=
  ∀ s : Fin r → cohomologyOverField k f E 0, LinearIndependent k s →
    Mono (evaluation k f E s) ∨ EverywhereRank (evaluation k f E s) (r - 1)

theorem completeSemiIrreducible_iff_top (E : X.Modules) (r : ℕ) :
    CompleteSemiIrreducible k f E r ↔ SemiIrreducible k f E r ⊤ := by
  constructor
  · intro h s hs
    exact h (fun i => (s i : cohomologyOverField k f E 0))
      (hs.map' (⊤ : Submodule k (cohomologyOverField k f E 0)).subtype
        (by simp))
  · intro h s hs
    let t : Fin r → (⊤ : Submodule k (cohomologyOverField k f E 0)) :=
      fun i => ⟨s i, Submodule.mem_top⟩
    have ht : LinearIndependent k t :=
      LinearIndependent.of_comp (⊤ : Submodule k (cohomologyOverField k f E 0)).subtype hs
    exact h t ht

/-- A complete semi-irreducible system restricts to every actual section
subspace, without changing its underlying sheaf evaluation maps. -/
theorem CompleteSemiIrreducible.restrict {E : X.Modules} {r : ℕ}
    (h : CompleteSemiIrreducible k f E r)
    (A : Submodule k (cohomologyOverField k f E 0)) :
    SemiIrreducible k f E r A := by
  intro s hs
  exact h (fun i => (s i : cohomologyOverField k f E 0))
    (hs.map' A.subtype (by simp))

/-- The basis form tests every `r`-dimensional actual section subspace.
The evaluation is written in the chosen basis of that subspace. -/
theorem semiIrreducible_basis {E : X.Modules} {r : ℕ}
    {A : Submodule k (cohomologyOverField k f E 0)}
    (h : SemiIrreducible k f E r A) (U : Submodule k A)
    (b : Module.Basis (Fin r) k U) :
    Mono (evaluation k f E (fun i => ((b i : A) : cohomologyOverField k f E 0))) ∨
      EverywhereRank
        (evaluation k f E (fun i => ((b i : A) : cohomologyOverField k f E 0))) (r - 1) := by
  exact h (fun i => (b i : A)) (b.linearIndependent.map' U.subtype (by simp))

section GlobalGeneration

/-- An actual sheaf is globally generated when a family of its genuine
compatible sections induces an epimorphism from the corresponding free
sheaf. No dimension predicate replaces that epimorphism. -/
def GloballyGenerated (E : X.Modules) : Prop := Nonempty E.GeneratingSections

/-- A Γ-split extension of globally generated actual sheaves is globally
generated. Generators of the quotient are lifted as actual global
sections, and combined with the images of generators of the subobject. -/
theorem globallyGenerated_extension (S : ShortComplex X.Modules)
    (hS : S.ShortExact)
    (hγ : Function.Surjective (_root_.SheafOfModules.sectionsMap S.g))
    (hQ : GloballyGenerated S.X₁) (hA : GloballyGenerated S.X₃) :
    GloballyGenerated S.X₂ := by
  classical
  obtain ⟨Q⟩ := hQ
  obtain ⟨A⟩ := hA
  choose l hl using fun j : A.I => hγ (A.s j)
  let τ : Q.I ⊕ A.I → S.X₂.sections :=
    Sum.elim (fun j => _root_.SheafOfModules.sectionsMap S.f (Q.s j)) l
  let v := S.X₂.freeHomEquiv.symm τ
  have hleft : _root_.SheafOfModules.freeMap Sum.inl ≫ v = Q.π ≫ S.f := by
    apply S.X₂.freeHomEquiv.injective
    funext j
    simp [v,τ,_root_.SheafOfModules.freeHomEquiv_comp_apply,
      _root_.SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection]
  have hright : _root_.SheafOfModules.freeMap Sum.inr ≫ v ≫ S.g = A.π := by
    apply S.X₃.freeHomEquiv.injective
    funext j
    simp [v,τ,_root_.SheafOfModules.freeHomEquiv_comp_apply,
      _root_.SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection,hl]
  have hv : Epi v := by
    rw [epi_iff_cancel_zero]
    intro T t ht
    have hi : S.f ≫ t = 0 := by
      apply (cancel_epi Q.π).mp
      calc
        Q.π ≫ (S.f ≫ t) = _root_.SheafOfModules.freeMap Sum.inl ≫ (v ≫ t) := by
          simpa only [Category.assoc] using congrArg (fun z => z ≫ t) hleft.symm
        _ = Q.π ≫ 0 := by rw [ht,comp_zero,comp_zero]
    let := hS.epi_g
    let b := hS.exact.desc t hi
    have hb : S.g ≫ b = t := hS.exact.g_desc t hi
    have hb0 : b = 0 := by
      apply (cancel_epi A.π).mp
      calc
        A.π ≫ b = _root_.SheafOfModules.freeMap Sum.inr ≫ (v ≫ t) := by
          rw [← hright,Category.assoc,Category.assoc,hb]
        _ = A.π ≫ 0 := by rw [ht,comp_zero,comp_zero]
    rw [← hb,hb0,comp_zero]
  exact ⟨⟨Q.I ⊕ A.I,τ,hv⟩⟩

/-- The actual dual-span bundle is globally generated: dualizing its
original short-exact evaluation sequence gives the required quotient of
the dual free sheaf, identified with the original free sheaf. -/
theorem dualSpan_globallyGenerated (β : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    (s : ULift.{u} (Fin 3) → β.sections)
    (hgen : Epi (MukaiBundle.netEvaluation β s)) :
    GloballyGenerated (MukaiBundle.dualSpan β s) := by
  obtain ⟨w,hS⟩ := MukaiBundle.dualEvaluationSequence_shortExact β s hgen
  let := hS.epi_g
  let q : MukaiBundle.netFree X ⟶ MukaiBundle.dualSpan β s :=
    (MukaiBundle.dualNetFreeIso X).inv ≫
      Stacks.AlgebraicGeometry.ReflexiveModules.dualMap
        (MukaiBundle.evaluationKernelInclusion β s)
  have hq : Epi q := by dsimp [q]; infer_instance
  let := hq
  exact ⟨(_root_.SheafOfModules.free.generatingSections
    (R := X.ringCatSheaf) (ULift.{u} (Fin 3))).ofEpi q⟩

/-- The global-generation assertion in Mukai Proposition 5.3 for its
original dual-span extension. Γ-splitting is the actual surjectivity on
compatible sheaf sections; no semi-irreducibility hypothesis is used. -/
theorem dualSpan_extension_globallyGenerated (β α E : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 β]
    (sβ : ULift.{u} (Fin 3) → β.sections)
    (hβ : Epi (MukaiBundle.netEvaluation β sβ))
    (sα : ULift.{u} (Fin 3) → α.sections)
    (hα : Epi (MukaiBundle.netEvaluation α sα))
    (i : MukaiBundle.dualSpan β sβ ⟶ E) (p : E ⟶ α)
    (w : i ≫ p = 0) (hS : (ShortComplex.mk i p w).ShortExact)
    (hγ : Function.Surjective (_root_.SheafOfModules.sectionsMap p)) :
    GloballyGenerated E := by
  exact globallyGenerated_extension (ShortComplex.mk i p w) hS hγ
    (dualSpan_globallyGenerated β sβ hβ) ⟨⟨ULift.{u} (Fin 3),sα,hα⟩⟩

end GlobalGeneration

end M9Native.MukaiSemiIrreducible
