module

public import M9StacksIntegration.AllTestSchemeFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# Variety properties of the actual represented original space

The represented space is the original Yoneda construction on every scheme
over the original field. Its separatedness is its genuine scheme diagonal;
its reducedness is tested on every actual etale chart. The identity atlas
retains the original structural morphism and its finite-type properties.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.StandaloneSchemeVariety
open AllTestSchemeFamilies
universe u
variable (K : Type u) [Field K]

local instance inverseImageStable (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] :
    (P.inverseImage (Over.forget (M9StandaloneDraft.Base K))).IsStableUnderBaseChange where
  of_isPullback h hp := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := P) (h.map (Over.forget (M9StandaloneDraft.Base K))) hp

/-- Yoneda carries the actual scheme diagonal to the original presheaf
diagonal through the canonical product comparison. -/
theorem yoneda_diagonal (X : M9StandaloneDraft.Schemes K) :
    yoneda.map (diag X) ≫ (PreservesLimitPair.iso yoneda X X).hom =
      diag (yoneda.obj X) := by
  apply prod.hom_ext
  · rw [Category.assoc, PreservesLimitPair.iso_hom, prodComparison_fst,
      ← Functor.map_comp]
    simp
  · rw [Category.assoc, PreservesLimitPair.iso_hom, prodComparison_snd,
      ← Functor.map_comp]
    simp

/-- The diagonal in schemes over the field is literally the relative
scheme diagonal, through the canonical product/pullback comparison. -/
theorem scheme_diagonal (X : M9StandaloneDraft.Schemes K) :
    (diag X).left ≫ (Over.prodLeftIsoPullback X X).hom =
      pullback.diagonal X.hom := by
  apply pullback.hom_ext
  · simp [← Over.comp_left]
  · simp [← Over.comp_left]

/-- The closed scheme diagonal gives closedness after every represented
base change of the original presheaf diagonal. -/
theorem diagonal_closed (X : M9StandaloneDraft.Schemes K) [IsSeparated X.hom] :
    (MorphismProperty.inverseImage (@IsClosedImmersion.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf
      (diag (standaloneSchemeSpace K X).obj) := by
  let Q : MorphismProperty (M9StandaloneDraft.Schemes K) :=
    MorphismProperty.inverseImage (@IsClosedImmersion.{u})
      (Over.forget (M9StandaloneDraft.Base K))
  have hd : IsClosedImmersion (diag X).left := by
    rw [(Iso.eq_comp_inv _).2 (scheme_diagonal K X)]
    infer_instance
  change Q.presheaf (diag (yoneda.obj X))
  rw [← yoneda_diagonal K X]
  exact (Q.presheaf.cancel_right_of_respectsIso _ _).mpr
    (MorphismProperty.relative_map (F := yoneda) (P := Q) hd)

/-- Every actual original etale chart of a reduced represented scheme is
reduced, with no size or finite-type restriction on the chart. -/
theorem etale_chart_reduced (X : M9StandaloneDraft.Schemes K) [IsReduced X.left]
    (V : M9StandaloneDraft.Schemes K) (v : yoneda.obj V ⟶ (standaloneSchemeSpace K X).obj)
    (hv : (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf v) : IsReduced V.left := by
  obtain ⟨f, rfl⟩ := yoneda.map_surjective v
  have : Etale f.left := MorphismProperty.of_relative_map (F := yoneda)
    (P := MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))) hv
  exact AlgebraicGeometry.isReduced_of_etale f.left

/-- A reduced separated finite-type scheme gives the actual original
variety-space property. The witness is its identity atlas. -/
theorem variety_of_reduced (X : M9StandaloneDraft.Schemes K) [IsReduced X.left]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    M9StandaloneDraft.VarietySpace K (standaloneSchemeSpace K X) := by
  refine ⟨diagonal_closed K X, etale_chart_reduced K X, X, 𝟙 _, ?_, ?_,
    inferInstance, inferInstance⟩
  · refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
    intro U V a b f h
    have : IsIso (yoneda.map f) := h.isIso_snd_of_isIso
    have : IsIso f := Yoneda.fullyFaithful.isIso_of_isIso_map f
    change Etale f.left
    infer_instance
  · refine ⟨Functor.relativelyRepresentable.of_isIso yoneda _, ?_⟩
    intro U V a b f h
    have : IsIso (yoneda.map f) := h.isIso_snd_of_isIso
    have : IsIso f := Yoneda.fullyFaithful.isIso_of_isIso_map f
    change Surjective f.left
    infer_instance

/-- In particular an integral separated finite-type scheme supplies the
standalone variety condition from its original scheme properties. -/
theorem variety_of_integral (X : M9StandaloneDraft.Schemes K) [IsIntegral X.left]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    M9StandaloneDraft.VarietySpace K (standaloneSchemeSpace K X) :=
  variety_of_reduced K X

end M9StacksIntegration.StandaloneSchemeVariety
