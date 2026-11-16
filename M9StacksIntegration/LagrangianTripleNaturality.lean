module

public import M9StacksIntegration.LagrangianUniversalTriples
public import M9StacksIntegration.SheafMapPullbackRank

/-! Actual original three-column evaluations are genuine pullbacks of
the original ambient universal quotient map. Thus their actual ranks
are the actual ambient ranks at the image, with no point or coordinate
comparison premise. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.LagrangianTripleNaturality

open LagrangianMatrixChart LagrangianUniversalSections LagrangianUniversalTriples
open AlgebraicGeometry.Grassmannian

variable (k : Type u) [Field k] {X Y : Scheme.{u}}

/-- The genuine structural coefficients commute with actual scheme pullback. -/
theorem baseRingMap_comp (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) :
    ExteriorEvaluation.baseRingMap k (g ≫ f) =
      g.appTop.hom.comp (ExteriorEvaluation.baseRingMap k f) := by
  have hf : f.appLE ⊤ ⊤ (by simp) = f.appTop := f.appLE_eq_app
  have hgf : (g ≫ f).appLE ⊤ ⊤ (by simp) = (g ≫ f).appTop := (g ≫ f).appLE_eq_app
  unfold ExteriorEvaluation.baseRingMap
  rw [hgf,hf]
  ext a
  simp only [Scheme.Hom.comp_appTop,CommRingCat.hom_comp,RingHom.comp_apply]

/-- The original constant three columns commute with the actual native free pullback isomorphisms. -/
theorem sourceMap_pullback (f : X ⟶ Spec (.of k)) (g : Y ⟶ X)
    (s : Fin 3 → (Fin 6 → k)) :
    (pullbackFreeIso g 3).inv ≫ (Scheme.Modules.pullback g).map (sourceMap k f s) ≫
      (pullbackFreeIso g 6).hom = sourceMap k (g ≫ f) s := by
  apply MukaiEvaluationMatrix.freeHom_ext_top
  intro j
  change (pullbackFreeIso g 6).hom.app ⊤
    (((Scheme.Modules.pullback g).map (sourceMap k f s)).app ⊤
      ((pullbackFreeIso g 3).inv.app ⊤ (freeBasisSection Y 3 j))) = _
  rw [PrimitiveFreeMatrixPullback.inverse_freeBasisSection_pullback,
    SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections,
    sourceMap_basis,sourceMap_basis]
  simp only [constantVector,map_sum,AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul,
    Scheme.Modules.Hom.app_smul,PrimitiveFreeMatrixPullback.freeBasisSection_pullback]
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun a => a • freeBasisSection Y 6 i)
    (RingHom.congr_fun (baseRingMap_comp k f g) (s j i)).symm

/-- The literal original ambient three-column evaluation before any scheme pullback. -/
def ambientEvaluation (s : Fin 3 → (Fin 6 → k)) :
    freeOn (LagrangianGrassmannian.space k) 3 ⟶ (LagrangianPluckerQuotient.quotientOnLG k).target :=
  sourceMap k (LagrangianGrassmannian.projection k) s ≫
    (LagrangianPluckerQuotient.quotientOnLG k).map

/-- The original actual H0 triple evaluation is the actual ambient evaluation pulled back. -/
theorem evaluation_eq_pullback (g : X ⟶ LagrangianGrassmannian.space k)
    (s : Fin 3 → (Fin 6 → k)) :
    evaluation k (g ≫ LagrangianGrassmannian.projection k) g s =
      (pullbackFreeIso g 3).inv ≫ (Scheme.Modules.pullback g).map (ambientEvaluation k s) := by
  rw [evaluation_eq_sourceMap_quotient]
  change sourceMap k (g ≫ LagrangianGrassmannian.projection k) s ≫
    ((pullbackFreeIso g 6).inv ≫
      (Scheme.Modules.pullback g).map (LagrangianPluckerQuotient.quotientOnLG k).map) = _
  have hs := sourceMap_pullback k (LagrangianGrassmannian.projection k) g s
  have h := congrArg (fun t => t ≫ (pullbackFreeIso g 6).inv ≫
    (Scheme.Modules.pullback g).map (LagrangianPluckerQuotient.quotientOnLG k).map) hs
  simpa only [ambientEvaluation,CategoryTheory.Functor.map_comp,Category.assoc,
    Iso.hom_inv_id_assoc] using h.symm

/-- Actual original triple rank is exactly actual ambient rank at the image point. -/
theorem evaluation_mapRankAt_eq_ambient (g : X ⟶ LagrangianGrassmannian.space k)
    (s : Fin 3 → (Fin 6 → k)) (x : X) :
    MukaiSemiIrreducible.mapRankAt
      (evaluation k (g ≫ LagrangianGrassmannian.projection k) g s) x =
      MukaiSemiIrreducible.mapRankAt (ambientEvaluation k s) (g x) := by
  rw [evaluation_eq_pullback]
  have h := FieldPointMapRankConsequences.mapRankAt_iso_conjugate
    ((Scheme.Modules.pullback g).map (ambientEvaluation k s)) (pullbackFreeIso g 3).symm
      (Iso.refl _) x
  simpa only [Iso.symm_hom,Iso.refl_hom,Category.comp_id] using
    h.trans (SheafMapPullbackRank.mapRankAt_pullback g (ambientEvaluation k s) x)

end M9Native.LagrangianTripleNaturality
