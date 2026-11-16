/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The scalar-compatibility proof for globalSectionsPullback is adapted from
the pinned StacksFrontier EnriquesSeveriZariski/SectionSelection.lean,
pullbackGlobalSectionsOverField. Its actual native section map is retained.
-/
module

public import M9StacksIntegration.MinimalDegreeSeriesGeneration
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.PullbackDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.NonpositiveDegreeSection
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Comparison

/-!
# Actual sections pull back injectively along a dominant curve map

A nonzero section of an invertible sheaf on an integral scheme has a
nonempty open nonvanishing locus. Dominance meets this open, and actual
pullback preserves nonvanishing. The resulting injection is transported
to native degree-zero cohomology by its original comparison maps, with
the actual base-field scalar compatibility proved explicitly.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace M9Native.PencilPullbackSections

variable {X Y : Scheme.{u}}

/-- The actual pullback of a nonzero line-bundle section remains nonzero
under a dominant morphism to an integral scheme. -/
theorem pullbackGlobalSections_ne_zero (g : X ⟶ Y) [IsDominant g] [IsIntegral Y]
    (M : Y.Modules)
    [hM : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property M]
    (s : Γ(M, ⊤)) (hs : s ≠ 0) : pullbackGlobalSections g M s ≠ 0 := by
  let t : M.sections := (Stacks.NonvanishingSpelling.sectionsEquiv Y M).symm s
  have ht : t.eval (op ⊤) = s :=
    (Stacks.NonvanishingSpelling.sectionsEquiv Y M).apply_symm_apply s
  have hUne := nonempty_nonvanishingLocus_of_eval_top_ne_zero M t (by rwa [ht])
  let : Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property M :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ M hM
  have hUopen := Stacks.SheafOfModules.isOpen_nonvanishingLocus
    (X := Y.toRingedSpace) M t
  change IsOpen (Stacks.SheafOfModules.nonvanishingLocus
    (X := Y.toRingedSpace) M ((Stacks.NonvanishingSpelling.sectionsEquiv Y M).symm s)) at hUopen
  rw [Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq] at hUopen
  change (Stacks.SheafOfModules.nonvanishingLocus
    (X := Y.toRingedSpace) M ((Stacks.NonvanishingSpelling.sectionsEquiv Y M).symm s)).Nonempty at hUne
  rw [Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq] at hUne
  have hdense : Dense (Set.range g.base) := (isDominant_iff g).mp inferInstance
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hdense.exists_mem_open hUopen hUne
  have hp := Stacks.TwistPullbackPinned.mem_nonvanishingLocus_pullbackGlobalSections g M s hx
  let P := (Scheme.Modules.pullback g).obj M
  let t' : P.sections := (Stacks.NonvanishingSpelling.sectionsEquiv X P).symm
    (pullbackGlobalSections g M s)
  have hx' : x ∈ Stacks.SheafOfModules.nonvanishingLocus
      (X := X.toRingedSpace) P t' := by
    change x ∈ Stacks.SheafOfModules.nonvanishingLocus
      (X := X.toRingedSpace) P ((Stacks.NonvanishingSpelling.sectionsEquiv X P).symm _)
    rw [Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq]
    exact hp
  have hn := eval_top_ne_zero_of_mem_nonvanishingLocus P t' hx'
  have ht' : t'.eval (op ⊤) = pullbackGlobalSections g M s :=
    (Stacks.NonvanishingSpelling.sectionsEquiv X P).apply_symm_apply _
  rwa [ht'] at hn

/-- The genuine global-section pullback is injective on a line bundle. -/
theorem pullbackGlobalSections_injective (g : X ⟶ Y) [IsDominant g] [IsIntegral Y]
    (M : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property M] :
    Function.Injective (pullbackGlobalSections g M) := by
  intro a b hab
  by_contra hne
  apply pullbackGlobalSections_ne_zero g M (a - b) (sub_ne_zero.mpr hne)
  simp only [map_sub, hab, sub_self]

/-- Native global sections with precisely the scalar restriction used
by the public degree-zero cohomology comparison. -/
abbrev fieldGlobalSections (k : Type u) [Field k]
    (pY : Y ⟶ Spec (.of k)) (M : Y.Modules) : ModuleCat.{u} k :=
  (restrictScalarsOverBase k pY).obj
    ((SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens))).obj M)

/-- Actual pullback on global sections with the original structure-map
scalar restriction. No transported replacement scalar action is used. -/
def globalSectionsPullback (k : Type u) [Field k]
    (pY : Y ⟶ Spec (.of k)) (g : X ⟶ Y) (M : Y.Modules) :
    fieldGlobalSections k pY M →ₗ[k]
      fieldGlobalSections k (g ≫ pY) ((Scheme.Modules.pullback g).obj M) where
  toFun s := pullbackGlobalSections g M s
  map_add' s t := map_add (ConcreteCategory.hom (pullbackGlobalSections g M)) s t
  map_smul' c s := by
    refine (SectionsEqualizer.pullbackGlobalSections_smul g M _ s).trans ?_
    congr 1
    have happ : g.appLE (⊤ : Y.Opens) (⊤ : X.Opens) (by simp) = g.appTop :=
      Scheme.Hom.appLE_eq_app g
    have h := Scheme.Hom.appLE_comp_appLE g pY (⊤ : (Spec (.of k)).Opens)
      (⊤ : Y.Opens) (⊤ : X.Opens) (by simp) (by simp)
    rw [happ] at h
    exact congrArg (fun φ => (CommRingCat.Hom.hom φ)
      ((Scheme.ΓSpecIso (.of k)).inv.hom c)) h

@[simp]
theorem globalSectionsPullback_apply (k : Type u) [Field k]
    (pY : Y ⟶ Spec (.of k)) (g : X ⟶ Y) (M : Y.Modules)
    (s : fieldGlobalSections k pY M) :
    globalSectionsPullback k pY g M s = pullbackGlobalSections g M s := rfl

/-- The native linear map on degree-zero cohomology induced by actual
pullback along a morphism over the original field. -/
def cohomologyPullback (k : Type u) [Field k]
    (pY : Y ⟶ Spec (.of k)) (g : X ⟶ Y) (M : Y.Modules) :
    cohomologyOverField k pY M 0 →ₗ[k]
      cohomologyOverField k (g ≫ pY) ((Scheme.Modules.pullback g).obj M) 0 :=
  (cohomologyOverFieldZeroLinearIso k (g ≫ pY) ((Scheme.Modules.pullback g).obj M)).inv.hom ∘ₗ
    globalSectionsPullback k pY g M ∘ₗ (cohomologyOverFieldZeroLinearIso k pY M).hom.hom

/-- The native cohomology pullback is injective on an actual line bundle
over the integral target of a dominant morphism. -/
theorem cohomologyPullback_injective (k : Type u) [Field k]
    (pY : Y ⟶ Spec (.of k)) (g : X ⟶ Y) [IsDominant g] [IsIntegral Y]
    (M : Y.Modules)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.property M] :
    Function.Injective (cohomologyPullback k pY g M) :=
  (cohomologyOverFieldZeroLinearIso k (g ≫ pY)
    ((Scheme.Modules.pullback g).obj M)).toLinearEquiv.symm.injective.comp
      ((pullbackGlobalSections_injective g M).comp
        (cohomologyOverFieldZeroLinearIso k pY M).toLinearEquiv.injective)

end M9Native.PencilPullbackSections
