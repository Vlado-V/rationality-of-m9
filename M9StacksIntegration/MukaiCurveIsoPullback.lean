module

public import M9StacksIntegration.SheafMapPullbackRank
public import StacksFrontier.AlgebraicGeometry.Modules.SectionsTransportAlongIso
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.FreePresentation
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.GlobalGeneration

/-!
# Complete native section systems under an isomorphism of curves

The actual pullback-pushforward unit transports global sections along a
scheme isomorphism over the original field. Its degree-zero cohomology
comparison is linear for that field and carries the original evaluation
map to the actual pulled-back evaluation map. Thus global generation and
complete semi-irreducibility transfer, without a section-space or
evaluation compatibility assumption.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Opposite

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.MukaiCurveIsoPullback

open MukaiSemiIrreducible

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  (e : X ≅ Y) (he : e.hom ≫ g = f)

/-- The actual adjunction unit, an isomorphism because the scheme map
is an isomorphism, gives the original scalar-preserving section map. -/
def sectionsPullbackIso (E : Y.Modules) :
    (restrictScalarsOverBase k g).obj
        ((SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens))).obj E) ≅
      (restrictScalarsOverBase k f).obj
        ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj
          ((Scheme.Modules.pullback e.hom).obj E)) := by
  let η := (Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app E
  letI : IsIso η := inferInstance
  refine (restrictScalarsOverBase k g).mapIso
      ((SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens))).mapIso (asIso η)) ≪≫ ?_
  exact (ModuleCat.restrictScalarsComp'App
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appLE ⊤ ⊤ (by simp)).hom e.hom.appTop.hom
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom
    (by
      rw [← CommRingCat.hom_comp]
      refine congrArg CommRingCat.Hom.hom ?_
      rw [Category.assoc, ← Scheme.Hom.appLE_comp_top e.hom g (by simp) (by simp), he])
    ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj
      ((Scheme.Modules.pullback e.hom).obj E))).symm

/-- This is the original pullback of a section, not an arbitrary
linear isomorphism between spaces of equal dimension. -/
theorem sectionsPullbackIso_apply (E : Y.Modules)
    (s : Γ(E, ⊤)) :
    (sectionsPullbackIso k f g e he E).hom s =
      pullbackGlobalSections e.hom E s := by
  change ((Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app E).val.app
      (op (⊤ : Y.Opens)) s = _
  symm
  change ((Scheme.Modules.pullback e.hom).obj E).presheaf.map
      (𝟙 (op (⊤ : X.Opens)))
      (((Scheme.Modules.pullbackPushforwardAdjunction e.hom).unit.app E).val.app
        (op (⊤ : Y.Opens)) s) = _
  exact Functor.map_id_apply _ _ _

/-- The actual native zeroth cohomology spaces, over the original
field, are identified by pullback. -/
def h0PullbackEquiv (E : Y.Modules) :
    cohomologyOverField k g E 0 ≃ₗ[k]
      cohomologyOverField k f ((Scheme.Modules.pullback e.hom).obj E) 0 :=
  (cohomologyOverFieldZeroLinearIso k g E).toLinearEquiv.trans
    ((sectionsPullbackIso k f g e he E).toLinearEquiv.trans
      (cohomologyOverFieldZeroLinearIso k f
        ((Scheme.Modules.pullback e.hom).obj E)).symm.toLinearEquiv)

theorem h0PullbackEquiv_section (E : Y.Modules)
    (s : cohomologyOverField k g E 0) :
    (cohomologyOverFieldZeroLinearIso k f
      ((Scheme.Modules.pullback e.hom).obj E)).hom
        (h0PullbackEquiv k f g e he E s) =
      pullbackGlobalSections e.hom E
        ((cohomologyOverFieldZeroLinearIso k g E).hom s) := by
  change (cohomologyOverFieldZeroLinearIso k f
      ((Scheme.Modules.pullback e.hom).obj E)).hom
        ((cohomologyOverFieldZeroLinearIso k f
          ((Scheme.Modules.pullback e.hom).obj E)).inv
            ((sectionsPullbackIso k f g e he E).hom
              ((cohomologyOverFieldZeroLinearIso k g E).hom s))) = _
  exact ((cohomologyOverFieldZeroLinearIso k f
    ((Scheme.Modules.pullback e.hom).obj E)).inv_hom_id_apply _).trans
      (sectionsPullbackIso_apply k f g e he E _)

include he in
theorem finrank_h0_pullback (E : Y.Modules) :
    Module.finrank k (cohomologyOverField k f ((Scheme.Modules.pullback e.hom).obj E) 0) =
      Module.finrank k (cohomologyOverField k g E 0) :=
  (h0PullbackEquiv k f g e he E).finrank_eq.symm

/-- The complete tuple evaluation commutes with actual pullback and
the canonical free-sheaf comparison. -/
theorem evaluation_pullback (E : Y.Modules) {r : ℕ}
    (s : Fin r → cohomologyOverField k g E 0) :
    (Grassmannian.pullbackFreeIso e.hom r).inv ≫
        (Scheme.Modules.pullback e.hom).map (MukaiSemiIrreducible.evaluation k g E s) =
      MukaiSemiIrreducible.evaluation k f ((Scheme.Modules.pullback e.hom).obj E)
        (fun i => h0PullbackEquiv k f g e he E (s i)) := by
  apply ((Scheme.Modules.pullback e.hom).obj E).freeHomEquiv.injective
  funext i
  apply (Stacks.NonvanishingSpelling.sectionsEquiv X
    ((Scheme.Modules.pullback e.hom).obj E)).injective
  rw [Stacks.ProjectiveFromSections.freeHomEquiv_pullbackFreeIso_inv]
  simp only [MukaiSemiIrreducible.evaluation, Equiv.apply_symm_apply]
  change pullbackGlobalSections e.hom E
      ((sectionOfH0 k g E (s i.down)).eval (op ⊤)) =
    (sectionOfH0 k f ((Scheme.Modules.pullback e.hom).obj E)
      (h0PullbackEquiv k f g e he E (s i.down))).eval (op ⊤)
  rw [sectionOfH0_eval_top, sectionOfH0_eval_top]
  exact (h0PullbackEquiv_section k f g e he E _).symm

/-- This is the original residue-field rank of the original tuple
evaluation, with its actual point transported by the scheme map. -/
theorem mapRankAt_evaluation_pullback (E : Y.Modules) {r : ℕ}
    (s : Fin r → cohomologyOverField k g E 0) (x : X) :
    mapRankAt (MukaiSemiIrreducible.evaluation k f ((Scheme.Modules.pullback e.hom).obj E)
      (fun i => h0PullbackEquiv k f g e he E (s i))) x =
        mapRankAt (MukaiSemiIrreducible.evaluation k g E s) (e.hom x) := by
  rw [← evaluation_pullback k f g e he E s]
  have h := FieldPointMapRankConsequences.mapRankAt_iso_conjugate
    ((Scheme.Modules.pullback e.hom).map (MukaiSemiIrreducible.evaluation k g E s))
    (Grassmannian.pullbackFreeIso e.hom r).symm
    (Iso.refl ((Scheme.Modules.pullback e.hom).obj E)) x
  simpa only [Iso.symm_hom, Iso.refl_hom, Category.comp_id] using
    h.trans (SheafMapPullbackRank.mapRankAt_pullback e.hom
      (MukaiSemiIrreducible.evaluation k g E s) x)

include he in
/-- Every independent tuple on the pulled-back bundle comes from an
independent original tuple. Both alternatives in complete
semi-irreducibility are transported as actual sheaf statements. -/
theorem completeSemiIrreducible_pullback (E : Y.Modules) (r : ℕ)
    (hE : CompleteSemiIrreducible k g E r) :
    CompleteSemiIrreducible k f ((Scheme.Modules.pullback e.hom).obj E) r := by
  intro t ht
  let s : Fin r → cohomologyOverField k g E 0 :=
    fun i => (h0PullbackEquiv k f g e he E).symm (t i)
  have hs : LinearIndependent k s :=
    ht.map' (h0PullbackEquiv k f g e he E).symm.toLinearMap
      (LinearMap.ker_eq_bot.mpr (h0PullbackEquiv k f g e he E).symm.injective)
  have ht' : (fun i => h0PullbackEquiv k f g e he E (s i)) = t := by
    funext i
    exact (h0PullbackEquiv k f g e he E).apply_symm_apply (t i)
  have hev := evaluation_pullback k f g e he E s
  rw [ht'] at hev
  rcases hE s hs with hm | hr
  · left
    let := hm
    let : (Scheme.Modules.pullback e.hom).IsRightAdjoint :=
      (Scheme.Modules.pullbackEquivOfIso e).symm.toAdjunction.isRightAdjoint
    rw [← hev]
    infer_instance
  · right
    intro x
    have h := mapRankAt_evaluation_pullback k f g e he E s x
    rw [ht'] at h
    exact h.trans (hr (e.hom x))

/-- Native global generation is preserved by actual pullback. -/
theorem globallyGenerated_pullback (E : Y.Modules)
    (hE : GloballyGenerated E) :
    GloballyGenerated ((Scheme.Modules.pullback e.hom).obj E) := by
  obtain ⟨G⟩ := hE
  exact ⟨Stacks.AlgebraicGeometry.FlatBaseChange.pullbackGeneratingSections e.hom E G⟩

end M9Native.MukaiCurveIsoPullback
