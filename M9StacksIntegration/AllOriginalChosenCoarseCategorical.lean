module

public import M9StacksIntegration.AllOriginalChosenCoarseClassifier
public import M9StacksIntegration.AllOriginalChosenCoarseAffineAgreement
public import M9StacksIntegration.BoundedAffineFamilyValueAgreement
public import M9StacksIntegration.ChosenCoarseSameSiteUniversality
public import M9StacksIntegration.StandaloneFiniteTypeAtlasNativeRecovery
public import M9StacksIntegration.AllTestNativeOriginalEssentialImage
public import M9StacksIntegration.OriginalClassifierNativeCompatibility
public import M9StacksIntegration.GenusNineCoarseVariety

attribute [local instance 1100] CategoryTheory.Iso.isIso_inv
  CategoryTheory.IsIso.mono_of_iso

@[expose] public section

/-! Full categorical universality of the SAME original chosen coarse space.
Finite-type atlas recovery gives actual comparison maps between independently
chosen sites. Their actual inverse laws follow from the proved uniqueness
against native targets. Arbitrary original algebraic-space targets are then
recovered on an enlarged site. No all-test cutoff or coarse comparison is an
input. This is a legacy consumer of the frozen actual variety producer. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory Opposite

namespace M9Native.AllOriginalChosenCoarseCategorical
open AllOriginalChosenCoarseClassifier AllOriginalChosenCoarseAffineAgreement
  M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AllTestNativeOriginalFunctor
  M9StacksIntegration.AllTestNativeOriginalEssentialImage

universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K))) (g : ℕ) (hg : 2 ≤ g)

/-- Literal factorization on ALL original bases and families. -/
abbrev Factors {P Q : M9StandaloneDraft.Presheaves K}
    (c : M9StandaloneDraft.Classifier K g P) (d : M9StandaloneDraft.Classifier K g Q)
    (f : P ⟶ Q) : Prop :=
  ∀ (T : M9StandaloneDraft.Schemes K) (F : M9StandaloneDraft.Family K T g),
    f.app (op T) (c.value T F) = d.value T F

/-- Same-site universality transports along an actual target recovery iso.
Every recovery iso in the final application is constructed by actual atlas recovery. -/
theorem existsUnique_factor_of_recovery
    (c : M9StandaloneDraft.Classifier K g (space B hZ K hK g hg).obj)
    (hB : ∀ (T : BigFppfOver B (Spec (.of K)) hK)
      (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g),
      c.value ((boundedInclusion B K hK).obj T) F =
        BoundedOriginalFamilyCoarseValue.originalValue B hZ K hK g hg F)
    (N : AlgebraicSpaces B (Spec (.of K)) hK) (W : M9StandaloneDraft.Presheaves K)
    (e : (originalPresheafFunctor K B hK).obj N ≅ W)
    (d : M9StandaloneDraft.Classifier K g W) :
    ∃! f : (space B hZ K hK g hg).obj ⟶ W, Factors K g c d f := by
  let d' := M9StacksIntegration.OriginalClassifierNativeCompatibility.postcompose K g d e.inv
  obtain ⟨f, hf, hu⟩ :=
    ChosenCoarseSameSiteUniversality.existsUnique_factor B hZ K hK g hg c hB N d'
  refine ⟨f ≫ e.hom, ?_, ?_⟩
  · intro T F
    change e.hom.app (op T) (f.app (op T) (c.value T F)) = d.value T F
    rw [hf T F]
    exact Iso.inv_hom_id_apply (e.app (op T)) (d.value T F)
  · intro a ha
    have ha' : Factors K g c d' (a ≫ e.inv) := by
      intro T F
      change e.inv.app (op T) (a.app (op T) (c.value T F)) =
        e.inv.app (op T) (d.value T F)
      rw [ha T F]
    have h := hu (a ≫ e.inv) ha'
    apply (cancel_mono e.inv).mp
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h

variable (B' : BigFppfSite.{u}) (hZ' : B'.Contains integerBase)
  (hK' : B'.Contains (Spec (.of K)))

/-- Actual finite-type recovery constructs the unique all-family map between
coarse spaces chosen on ANY two sites over the same field. -/
theorem existsUnique_cross_site_map :
    ∃! f : (space B hZ K hK g hg).obj ⟶ (space B' hZ' K hK' g hg).obj,
      Factors K g (classifier B hZ K hK g hg) (classifier B' hZ' K hK' g hg) f := by
  obtain ⟨N, ⟨e⟩⟩ :=
    StandaloneFiniteTypeAtlasNativeRecovery.exists_native_recovery_of_native_finiteType
      K B hK B' hK'
      (M9StacksIntegration.GenusNineCoarseOverField.coarseSpace B' hZ' K hK' g hg)
      (GenusNineCoarseVariety.locallyFiniteType B' hZ' K hK' g hg)
      (GenusNineCoarseVariety.quasiCompact B' hZ' K hK' g hg)
  exact existsUnique_factor_of_recovery B hZ K hK g hg (classifier B hZ K hK g hg)
    (classifier_value_bounded B hZ K hK g hg) N (space B' hZ' K hK' g hg).obj e
    (classifier B' hZ' K hK' g hg)

/-- The actual comparison map; no comparison is supplied as input. -/
def crossSiteMap : (space B hZ K hK g hg).obj ⟶ (space B' hZ' K hK' g hg).obj :=
  (existsUnique_cross_site_map B hZ K hK g hg B' hZ' hK').choose

theorem crossSiteMap_factor :
    Factors K g (classifier B hZ K hK g hg) (classifier B' hZ' K hK' g hg)
      (crossSiteMap B hZ K hK g hg B' hZ' hK') :=
  (existsUnique_cross_site_map B hZ K hK g hg B' hZ' hK').choose_spec.1

theorem crossSiteMap_unique
    (f : (space B hZ K hK g hg).obj ⟶ (space B' hZ' K hK' g hg).obj)
    (hf : Factors K g (classifier B hZ K hK g hg) (classifier B' hZ' K hK' g hg) f) :
    f = crossSiteMap B hZ K hK g hg B' hZ' hK' :=
  (existsUnique_cross_site_map B hZ K hK g hg B' hZ' hK').choose_spec.2 f hf

/-- The independently chosen coarse spaces are actually isomorphic on ALL
original tests. Both inverse laws follow from proved all-family uniqueness. -/
def crossSiteIso : (space B hZ K hK g hg).obj ≅ (space B' hZ' K hK' g hg).obj where
  hom := crossSiteMap B hZ K hK g hg B' hZ' hK'
  inv := crossSiteMap B' hZ' K hK' g hg B hZ hK
  hom_inv_id := by
    have hc : Factors K g (classifier B hZ K hK g hg) (classifier B hZ K hK g hg)
        (crossSiteMap B hZ K hK g hg B' hZ' hK' ≫
          crossSiteMap B' hZ' K hK' g hg B hZ hK) := by
      intro T F
      change (crossSiteMap B' hZ' K hK' g hg B hZ hK).app (op T)
        ((crossSiteMap B hZ K hK g hg B' hZ' hK').app (op T)
          ((classifier B hZ K hK g hg).value T F)) = _
      rw [crossSiteMap_factor B hZ K hK g hg B' hZ' hK' T F,
        crossSiteMap_factor B' hZ' K hK' g hg B hZ hK T F]
    exact (crossSiteMap_unique B hZ K hK g hg B hZ hK _ hc).trans
      (crossSiteMap_unique B hZ K hK g hg B hZ hK (𝟙 _) (by intro T F; rfl)).symm
  inv_hom_id := by
    have hc : Factors K g (classifier B' hZ' K hK' g hg) (classifier B' hZ' K hK' g hg)
        (crossSiteMap B' hZ' K hK' g hg B hZ hK ≫
          crossSiteMap B hZ K hK g hg B' hZ' hK') := by
      intro T F
      change (crossSiteMap B hZ K hK g hg B' hZ' hK').app (op T)
        ((crossSiteMap B' hZ' K hK' g hg B hZ hK).app (op T)
          ((classifier B' hZ' K hK' g hg).value T F)) = _
      rw [crossSiteMap_factor B' hZ' K hK' g hg B hZ hK T F,
        crossSiteMap_factor B hZ K hK g hg B' hZ' hK' T F]
    exact (crossSiteMap_unique B' hZ' K hK' g hg B' hZ' hK' _ hc).trans
      (crossSiteMap_unique B' hZ' K hK' g hg B' hZ' hK' (𝟙 _) (by intro T F; rfl)).symm

theorem crossSiteIso_hom_factor :
    Factors K g (classifier B hZ K hK g hg) (classifier B' hZ' K hK' g hg)
      (crossSiteIso B hZ K hK g hg B' hZ' hK').hom :=
  crossSiteMap_factor B hZ K hK g hg B' hZ' hK'

theorem crossSiteIso_inv_factor :
    Factors K g (classifier B' hZ' K hK' g hg) (classifier B hZ K hK g hg)
      (crossSiteIso B hZ K hK g hg B' hZ' hK').inv :=
  crossSiteMap_factor B' hZ' K hK' g hg B hZ hK

/-- Universality for EVERY original algebraic-space target, with no common
fixed cutoff. Actual enlarged-site recovery and the derived comparison iso
construct and uniquely determine the original factor map. -/
theorem isCategorical : M9StandaloneDraft.IsCategorical K (classifier B hZ K hK g hg) := by
  classical
  intro W d
  obtain ⟨B₁, hK₁, hS, N, ⟨e⟩⟩ :=
    exists_site_original_recovery K W ({integerBase} : Set Scheme.{u})
  have hZ₁ : B₁.Contains integerBase := hS _ (by simp)
  obtain ⟨f₁, hf₁, hu₁⟩ :=
    existsUnique_factor_of_recovery B₁ hZ₁ K hK₁ g hg (classifier B₁ hZ₁ K hK₁ g hg)
      (classifier_value_bounded B₁ hZ₁ K hK₁ g hg) N W.obj e d
  let E := crossSiteIso B hZ K hK g hg B₁ hZ₁ hK₁
  refine ⟨E.hom ≫ f₁, ?_, ?_⟩
  · intro T F
    change f₁.app (op T) (E.hom.app (op T) ((classifier B hZ K hK g hg).value T F)) = _
    rw [crossSiteIso_hom_factor B hZ K hK g hg B₁ hZ₁ hK₁ T F, hf₁ T F]
  · intro a ha
    have ha' : Factors K g (classifier B₁ hZ₁ K hK₁ g hg) d (E.inv ≫ a) := by
      intro T F
      change a.app (op T) (E.inv.app (op T) ((classifier B₁ hZ₁ K hK₁ g hg).value T F)) = _
      rw [crossSiteIso_inv_factor B hZ K hK g hg B₁ hZ₁ hK₁ T F, ha T F]
    have hh := hu₁ (E.inv ≫ a) ha'
    calc
      a = E.hom ≫ (E.inv ≫ a) := by simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      _ = E.hom ≫ f₁ := congrArg (fun m => E.hom ≫ m) hh

end M9Native.AllOriginalChosenCoarseCategorical
