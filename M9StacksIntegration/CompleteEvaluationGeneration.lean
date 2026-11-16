module

public import M9StacksIntegration.MukaiDualSpanSections
public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalGeneration.Stalks
public import StacksFrontier.AlgebraicGeometry.FinGenFromCover.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Ratio

/-!
# A complete cohomology basis evaluates every global section

Evaluation of a finite complete native cohomology basis is surjective
on the original top sections. Any actual generating free evaluation
therefore factors through that evaluation, so it is epimorphic too.

No identification of the old bare cohomology comparison with the newer
linear comparison is used. The factorization lifts original top sections
and is checked as an equality of the original sheaf morphisms.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

universe u

namespace M9Native.CompleteEvaluationGeneration

open CategoryTheory AlgebraicGeometry Opposite

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The actual compatible sections obtained from a complete native
cohomology basis of any finite cardinality. -/
def basisSections (f : X ⟶ Spec (.of k)) (M : X.Modules) {I : Type u}
    (b : Module.Basis I k (cohomologyOverField k f M 0)) : I → M.sections := fun i =>
  Stacks.PresheafOfModules.sectionOfTop M.val
    ((cohomologyOverFieldZeroLinearIso k f M).hom (b i))

@[simp]
theorem basisSections_eval_top (f : X ⟶ Spec (.of k)) (M : X.Modules) {I : Type u}
    (b : Module.Basis I k (cohomologyOverField k f M 0)) (i : I) :
    (basisSections f M b i).eval (op ⊤) =
      (cohomologyOverFieldZeroLinearIso k f M).hom (b i) :=
  Stacks.PresheafOfModules.sectionOfTop_val_top _ _

def basisEvaluation (f : X ⟶ Spec (.of k)) (M : X.Modules) {I : Type u}
    (b : Module.Basis I k (cohomologyOverField k f M 0)) :
    (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules) ⟶ M :=
  M.freeHomEquiv.symm (basisSections f M b)

/-- Every original global section is evaluated from the original free
source. This needs no properness or constants-isomorphism hypothesis. -/
theorem basisEvaluation_top_surjective (f : X ⟶ Spec (.of k)) (M : X.Modules)
    {I : Type u} [Fintype I] (b : Module.Basis I k (cohomologyOverField k f M 0)) :
    Function.Surjective ((basisEvaluation f M b).val.app (op ⊤)) := by
  classical
  let ρ : k →+* Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom
  let T := (restrictScalarsOverBase k f).obj
    ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj M)
  let e : cohomologyOverField k f M 0 ≃ₗ[k] T :=
    (cohomologyOverFieldZeroLinearIso k f M).toLinearEquiv
  intro σ
  let v := e.symm σ
  let a : I → Γ(X, ⊤) := fun i => ρ (b.repr v i)
  refine ⟨Stacks.SheafOfModules.freeMk (S := X.ringCatSheaf) (op ⊤) a, ?_⟩
  calc
    _ = ∑ i, a i • (basisSections f M b i).eval (op ⊤) := by
      simpa only [Stacks.SheafOfModules.freeCoord_freeMk, basisEvaluation,
        Equiv.apply_symm_apply] using
        Stacks.SheafOfModules.app_eq_sum_smul_freeCoord (basisEvaluation f M b) (op ⊤)
          (Stacks.SheafOfModules.freeMk (S := X.ringCatSheaf) (op ⊤) a)
    _ = e v := by
      simp only [basisSections_eval_top]
      change ∑ i, b.repr v i • e (b i) = e v
      simpa only [map_sum, map_smul] using congrArg e (b.sum_repr v)
    _ = σ := e.apply_symm_apply σ

/-- If an actual free evaluation already generates M, any sheaf map
onto its original top sections receives a factorization of that same
generating evaluation, and is therefore epimorphic. -/
theorem epi_of_freeEvaluation_of_top_surjective {F M : X.Modules} (q : F ⟶ M)
    (hq : Function.Surjective (q.app ⊤)) {J : Type u} (t : J → M.sections)
    (hgen : Epi (M.freeHomEquiv.symm t)) : Epi q := by
  classical
  choose z hz using fun j => hq ((t j).eval (op ⊤))
  let τ : J → F.sections := fun j => Stacks.PresheafOfModules.sectionOfTop F.val (z j)
  have hτ (j : J) : SheafOfModules.sectionsMap q (τ j) = t j := by
    apply Stacks.PresheafOfModules.sections_ext_top
    change q.app ⊤ ((Stacks.PresheafOfModules.sectionOfTop F.val (z j)).val (op ⊤)) =
      (t j).eval (op ⊤)
    rw [Stacks.PresheafOfModules.sectionOfTop_val_top]
    exact hz j
  have hcomp : F.freeHomEquiv.symm τ ≫ q = M.freeHomEquiv.symm t := by
    rw [SheafOfModules.freeHomEquiv_symm_comp]
    congr 1
    funext j
    exact hτ j
  let : Epi (F.freeHomEquiv.symm τ ≫ q) := hcomp.symm ▸ hgen
  exact epi_of_epi (F.freeHomEquiv.symm τ) q

/-- A complete basis evaluates epimorphically whenever the actual module
has any actual generating free evaluation. -/
theorem basisEvaluation_epi_of_freeEvaluation_epi (f : X ⟶ Spec (.of k)) (M : X.Modules)
    {I : Type u} [Fintype I] (b : Module.Basis I k (cohomologyOverField k f M 0))
    {J : Type u} (t : J → M.sections) (hgen : Epi (M.freeHomEquiv.symm t)) :
    Epi (basisEvaluation f M b) :=
  epi_of_freeEvaluation_of_top_surjective _ (basisEvaluation_top_surjective f M b) t hgen

/-- Exact specialization to the original complete-net spelling used by
the dual-span construction and its divisor sequence. -/
theorem completeNetEvaluation_epi_of_freeEvaluation_epi
    (f : X ⟶ Spec (.of k)) (M : X.Modules)
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f M 0))
    {J : Type u} (t : J → M.sections) (hgen : Epi (M.freeHomEquiv.symm t)) :
    Epi (MukaiBundle.netEvaluation M (MukaiDualSpanSections.completeNetSections f M b)) :=
  basisEvaluation_epi_of_freeEvaluation_epi f M b t hgen

/-- The forward free-presentation argument uses only the already
checked stalkwise-generation and rank-one nonvanishing providers. It
is the small forward half of the native `FreePresentation` proof, not
its unrelated pullback-comparison closure. -/
theorem freeEvaluation_epi_of_generatesStalks (M : X.Modules)
    [hM : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property M]
    {J : Type u} (t : J → Γ(M, ⊤))
    (ht : Stacks.ProjectiveFromSections.GeneratesStalks t) :
    Epi (M.freeHomEquiv.symm
      (fun j => (Stacks.NonvanishingSpelling.sectionsEquiv X M).symm (t j))) := by
  let : Stacks.Ample.IsInvertibleModule X M := hM
  refine (AlgebraicGeometry.generates_iff_stalkwise_generates X.ringCatSheaf M _).mpr fun x => ?_
  obtain ⟨j, hj⟩ := Stacks.ProjectiveFromSections.exists_mem_nvCover_of_generatesStalks t ht x
  have heval (j : J) :
      ((Stacks.NonvanishingSpelling.sectionsEquiv X M).symm (t j)).eval (op ⊤) = t j :=
    (Stacks.NonvanishingSpelling.sectionsEquiv X M).apply_symm_apply (t j)
  simp only [heval]
  exact Stacks.FinGenFromCover.span_eq_top_of_mem_nonvanishingLocus M t hj

/-- Any generating original family proves epimorphy of evaluation of
any complete native cohomology basis. -/
theorem basisEvaluation_epi_of_generatesStalks (f : X ⟶ Spec (.of k)) (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property M]
    {I : Type u} [Fintype I] (b : Module.Basis I k (cohomologyOverField k f M 0))
    {J : Type u} (t : J → Γ(M, ⊤))
    (ht : Stacks.ProjectiveFromSections.GeneratesStalks t) : Epi (basisEvaluation f M b) :=
  basisEvaluation_epi_of_freeEvaluation_epi f M b
    (fun j => (Stacks.NonvanishingSpelling.sectionsEquiv X M).symm (t j))
    (freeEvaluation_epi_of_generatesStalks M t ht)

theorem completeNetEvaluation_epi_of_generatesStalks
    (f : X ⟶ Spec (.of k)) (M : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property M]
    (b : Module.Basis (ULift.{u} (Fin 3)) k (cohomologyOverField k f M 0))
    {J : Type u} (t : J → Γ(M, ⊤))
    (ht : Stacks.ProjectiveFromSections.GeneratesStalks t) :
    Epi (MukaiBundle.netEvaluation M (MukaiDualSpanSections.completeNetSections f M b)) :=
  basisEvaluation_epi_of_generatesStalks f M b t ht

/-- The original finite generating family may be indexed in the module
universe without changing its actual global sections or stalk span. -/
theorem generatesStalks_ulift (M : X.Modules) {n : ℕ} (t : Fin n → Γ(M, ⊤))
    (ht : Stacks.ProjectiveFromSections.GeneratesStalks t) :
    Stacks.ProjectiveFromSections.GeneratesStalks
      (fun i : ULift.{u} (Fin n) => t i.down) := by
  intro x w
  obtain ⟨s, r, hw⟩ := ht x w
  refine ⟨s.map (Equiv.ulift.{u}).symm.toEmbedding, fun i => r i.down, ?_⟩
  rwa [Finset.sum_map]

end M9Native.CompleteEvaluationGeneration
