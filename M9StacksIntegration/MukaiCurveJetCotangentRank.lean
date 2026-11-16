module

public import M9StacksIntegration.MukaiEvaluationCurveJetFrames
public import M9StacksIntegration.MukaiConormalChartJetRank
public import M9StacksIntegration.CurveTangentLineGeometry
public import M9StacksIntegration.SectionCokernelField
public import M9StacksIntegration.FieldPointMapRank

/-!
# Actual cotangent rank in a pulled chart of the curve

The native differential square, rather than a supplied rank comparison,
transports rank one of the original LG differential to surjectivity on
the genuine curve-point cotangent line.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.MukaiCurveJetCotangentRank

open MukaiEvaluationCurveJetChainRule MukaiConormalChartJets

private theorem finrank_range_eq_zero_of_eq_zero {F V W : Type u} [Field F]
    [AddCommGroup V] [AddCommGroup W] [Module F V] [Module F W]
    (a : V →ₗ[F] W) (ha : a = 0) : finrank F (LinearMap.range a) = 0 := by
  rw [ha, LinearMap.range_zero, finrank_bot]

variable (K : Type u) [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (u : Y ⟶ X)

/-- The original native differential of the étale curve restriction. -/
def restrictionDifferential :=
  Scheme.Hom.relativeDifferentialsMap u f (u ≫ f) (𝟙 _) (by simp)

instance restrictionDifferential_isIso [Etale u] :
    IsIso (restrictionDifferential K f u) :=
  Scheme.Hom.isIso_relativeDifferentialsMap_of_etale u f (u ≫ f) (𝟙 _) (by simp)

theorem pointCotangent_finite_and_finrank [IsCurve K f] [Smooth f] [Etale u]
    (z : Spec (.of K) ⟶ Y) :
    Module.Finite K (MukaiEvaluationCurveJets.PointCotangent K (u ≫ f) z) ∧
      finrank K (MukaiEvaluationCurveJets.PointCotangent K (u ≫ f) z) = 1 := by
  let : IsIso (restrictionDifferential K f u) := restrictionDifferential_isIso K f u
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Scheme.Hom.relativeDifferentials f) 1 :=
    CurveTangentLineGeometry.differentials_rank_one f
  have hu := isFiniteLocallyFreeOfRank_pullback u (Scheme.Hom.relativeDifferentials f) 1
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Scheme.Hom.relativeDifferentials (u ≫ f)) 1 :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      (asIso (restrictionDifferential K f u)) hu
  let := isFiniteLocallyFreeOfRank_pullback z (Scheme.Hom.relativeDifferentials (u ≫ f)) 1
  exact MukaiConormalFieldCoordinates.finite_and_finrank_sections K _ 1

variable [CharZero K] [IsAlgClosed K]
    (a : X ⟶ LagrangianGrassmannian.space K)
    (ha : a ≫ LagrangianGrassmannian.projection K = f)
    (h : chart K ⟶ LagrangianGrassmannian.space K)
    (hh : h ≫ LagrangianGrassmannian.projection K = chartProjection K)
    (γ : Y ⟶ chart K) (hγ : γ ≫ chartProjection K = u ≫ f)
    (hfactor : γ ≫ h = u ≫ a)

/-- The original differential of the original curve-to-LG map. -/
def originalDifferential :=
  Scheme.Hom.relativeDifferentialsMap a (LagrangianGrassmannian.projection K) f
    (𝟙 _) (by simpa using ha)

include hfactor in
omit [CharZero K] [IsAlgClosed K] in
/-- The actual native differential square, including its original
pullback-composition and pullback-congruence comparisons. -/
theorem differential_square :
    (LineFramePullback.squareIso γ h u a hfactor
      (Scheme.Hom.relativeDifferentials (LagrangianGrassmannian.projection K))).hom ≫
        (Scheme.Modules.pullback u).map (originalDifferential K f a ha) ≫
          restrictionDifferential K f u =
      (Scheme.Modules.pullback γ).map
        (MukaiConormalChartDifferential.nativeDifferential K h hh) ≫
          cotangentDifferential K (u ≫ f) γ hγ := by
  have hu := RelativeDifferentialsSpatialComposition.relativeDifferentialsMap_spatial_comp
    u a (LagrangianGrassmannian.projection K) f (u ≫ f) (𝟙 _) (𝟙 _)
    (by simpa using ha) (by simp) (by simp [Category.assoc, ha])
  have hs := RelativeDifferentialsSpatialComposition.relativeDifferentialsMap_spatial_comp_hom
    γ h (u ≫ a) hfactor (LagrangianGrassmannian.projection K)
    (chartProjection K) (u ≫ f) (𝟙 _) (𝟙 _)
    (by simpa using hh) (by simpa using hγ) (by simp [Category.assoc, ha])
  have hu' :
      (Scheme.Modules.pullbackComp u a).inv.app
          (Scheme.Hom.relativeDifferentials (LagrangianGrassmannian.projection K)) ≫
        ((Scheme.Modules.pullback u).map (originalDifferential K f a ha) ≫
          restrictionDifferential K f u) =
      Scheme.Hom.relativeDifferentialsMap (u ≫ a) (LagrangianGrassmannian.projection K)
        (u ≫ f) (𝟙 _ ≫ 𝟙 _) (by simp [Category.assoc, ha]) := hu
  rw [← hu'] at hs
  simpa only [LineFramePullback.squareIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Iso.app_inv, Category.assoc, originalDifferential, restrictionDifferential,
    MukaiConormalChartDifferential.nativeDifferential, cotangentDifferential] using hs

omit [CharZero K] [IsAlgClosed K] in
theorem original_pullback_ne_zero (z : Spec (.of K) ⟶ Y)
    (hr : MukaiSemiIrreducible.mapRankAt (originalDifferential K f a ha)
      ((z ≫ u) (SpecFieldStalkSections.point K)) = 1) :
    (Scheme.Modules.pullback (z ≫ u)).map (originalDifferential K f a ha) ≠ 0 := by
  intro hz
  have hd := (FieldPointMapRank.finrank_range_pullbackSections_eq_mapRankAt K
    (originalDifferential K f a ha) (z ≫ u)).trans hr
  have hzero : (moduleSpecΓFunctor.map
      ((Scheme.Modules.pullback (z ≫ u)).map (originalDifferential K f a ha))).hom = 0 := by
    rw [hz]
    rfl
  have hd0 := finrank_range_eq_zero_of_eq_zero _ hzero
  exact Nat.zero_ne_one (hd0.symm.trans hd)

theorem iterated_pullback_ne_zero (z : Spec (.of K) ⟶ Y)
    (hr : MukaiSemiIrreducible.mapRankAt (originalDifferential K f a ha)
      ((z ≫ u) (SpecFieldStalkSections.point K)) = 1) :
    (Scheme.Modules.pullback z).map
      ((Scheme.Modules.pullback u).map (originalDifferential K f a ha)) ≠ 0 := by
  intro hz
  apply original_pullback_ne_zero K f u a ha z hr
  apply (cancel_epi ((Scheme.Modules.pullbackComp z u).hom.app
    ((Scheme.Modules.pullback a).obj
      (Scheme.Hom.relativeDifferentials (LagrangianGrassmannian.projection K))))).mp
  have hn := (Scheme.Modules.pullbackComp z u).hom.naturality (originalDifferential K f a ha)
  change (Scheme.Modules.pullback z).map
      ((Scheme.Modules.pullback u).map (originalDifferential K f a ha)) ≫
      (Scheme.Modules.pullbackComp z u).hom.app (Scheme.Hom.relativeDifferentials f) =
    (Scheme.Modules.pullbackComp z u).hom.app
      ((Scheme.Modules.pullback a).obj
        (Scheme.Hom.relativeDifferentials (LagrangianGrassmannian.projection K))) ≫
      (Scheme.Modules.pullback (z ≫ u)).map (originalDifferential K f a ha) at hn
  simpa only [hz, zero_comp, comp_zero] using hn.symm

include hh hfactor in
theorem curve_pullback_ne_zero [Etale u] (z : Spec (.of K) ⟶ Y)
    (hr : MukaiSemiIrreducible.mapRankAt (originalDifferential K f a ha)
      ((z ≫ u) (SpecFieldStalkSections.point K)) = 1) :
    (Scheme.Modules.pullback z).map (cotangentDifferential K (u ≫ f) γ hγ) ≠ 0 := by
  let : IsIso (restrictionDifferential K f u) := restrictionDifferential_isIso K f u
  intro hz
  have hs := congrArg ((Scheme.Modules.pullback z).map)
    (differential_square K f u a ha h hh γ hγ hfactor)
  have hzero :
      (Scheme.Modules.pullback z).map
          (LineFramePullback.squareIso γ h u a hfactor
            (Scheme.Hom.relativeDifferentials (LagrangianGrassmannian.projection K))).hom ≫
        (Scheme.Modules.pullback z).map
          ((Scheme.Modules.pullback u).map (originalDifferential K f a ha)) ≫
          (Scheme.Modules.pullback z).map (restrictionDifferential K f u) = 0 := by
    simpa only [Functor.map_comp, hz, comp_zero] using hs
  apply iterated_pullback_ne_zero K f u a ha z hr
  apply (cancel_epi ((Scheme.Modules.pullback z).map
    (LineFramePullback.squareIso γ h u a hfactor
      (Scheme.Hom.relativeDifferentials (LagrangianGrassmannian.projection K))).hom)).mp
  apply (cancel_mono ((Scheme.Modules.pullback z).map (restrictionDifferential K f u))).mp
  simpa only [Category.assoc, comp_zero, zero_comp] using hzero

include hh hfactor in
/-- The actual point cotangent map is onto, derived from the original
differential rank and the genuine curve cotangent line. -/
theorem pointCotangentMap_surjective_of_rank_one [IsCurve K f] [Smooth f] [Etale u]
    (z : Spec (.of K) ⟶ Y)
    (hr : MukaiSemiIrreducible.mapRankAt (originalDifferential K f a ha)
      ((z ≫ u) (SpecFieldStalkSections.point K)) = 1) :
    Function.Surjective (pointCotangentMap K (u ≫ f) γ hγ z) := by
  have hc : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (chartCotangent K) 6 :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      (LagrangianChartCotangent.affineCotangentIso K).symm
      (SheafOfModules.isFiniteLocallyFreeOfRank_free (R := (chart K).ringCatSheaf) 6)
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback (z ≫ γ)).obj (chartCotangent K)) 6 :=
    @isFiniteLocallyFreeOfRank_pullback _ _ (z ≫ γ) _ 6 hc
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      ((Scheme.Modules.pullback (z ≫ γ)).obj (chartCotangent K)) :=
    (inferInstance : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback (z ≫ γ)).obj (chartCotangent K)) 6).isFiniteLocallyFree
  let : ((Scheme.Modules.pullback (z ≫ γ)).obj (chartCotangent K)).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree _
  have hn : (Scheme.Modules.pullbackComp z γ).inv.app (chartCotangent K) ≫
      (Scheme.Modules.pullback z).map (cotangentDifferential K (u ≫ f) γ hγ) ≠ 0 := by
    intro hz
    apply curve_pullback_ne_zero K f u a ha h hh γ hγ hfactor z hr
    apply (cancel_epi ((Scheme.Modules.pullbackComp z γ).inv.app (chartCotangent K))).mp
    simpa only [comp_zero] using hz
  have hΓ := SectionCokernelLocallyFree.gamma_map_ne_zero _ hn
  have hlin : pointCotangentMap K (u ≫ f) γ hγ z ≠ 0 := by
    intro hz
    exact hΓ (ModuleCat.hom_ext hz)
  obtain ⟨hfin,hdim⟩ := pointCotangent_finite_and_finrank K f u z
  let := hfin
  exact surjective_of_nonzero_of_finrank_eq_one hdim hlin

end M9Native.MukaiCurveJetCotangentRank
