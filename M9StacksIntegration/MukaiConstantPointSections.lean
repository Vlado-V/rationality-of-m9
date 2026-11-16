module

public import M9StacksIntegration.MukaiEvaluationCurveJets
public import M9StacksIntegration.MukaiConstantLinearCoordinates
public import M9StacksIntegration.MukaiConormalFieldCoordinates

/-! Actual constant-module sections at a same-base field point. The
comparison is computed in the original finite basis using the genuine
free pullback map; its naturality is the original sheaf-map naturality.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

namespace M9Native.MukaiConstantPointSections

open MukaiCubicConstantSheaf MukaiConstantFreeBasis MukaiConstantLinearCoordinates
open MukaiFreePullbackCoordinates MukaiEvaluationCurveJets MukaiConormalFieldCoordinates
open LagrangianMatrixChart AlgebraicGeometry.Grassmannian SectionZeroIdealFactorization

variable (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)

abbrev PointModule (M : ModuleCat.{u} K) :=
  moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj (constantObj (.of K) f M))

theorem constantSection_smul (M : ModuleCat.{u} K) (a : K) (m : M) :
    constantSection (.of K) f M (a • m) =
      MukaiConstantFreeBasis.baseScalar (.of K) f a • constantSection (.of K) f M m :=
  pulled_topSec_smul (.of K) f M a m

def pointConstantSection (M : ModuleCat.{u} K) : M →ₗ[K] PointModule K f p M where
  toFun m := pullbackGlobalSections p (constantObj (.of K) f M) (constantSection (.of K) f M m)
  map_add' m n := by
    unfold constantSection
    rw [map_add, map_add, map_add]
  map_smul' a m := by
    change pullbackGlobalSections p (constantObj (.of K) f M) (constantSection (.of K) f M (a • m)) =
      (Scheme.ΓSpecIso (.of K)).inv.hom a •
        pullbackGlobalSections p (constantObj (.of K) f M) (constantSection (.of K) f M m)
    rw [constantSection_smul, SectionsEqualizer.pullbackGlobalSections_smul,
      fieldPoint_baseScalar K f p hp]

def pointBasisIso (M : ModuleCat.{u} K) (r : ℕ) (b : Basis (Fin r) K M) :
    (Scheme.Modules.pullback p).obj (constantObj (.of K) f M) ≅ freeOn (Spec (.of K)) r :=
  (Scheme.Modules.pullback p).mapIso (basisIso (.of K) f M r b) ≪≫ pullbackFreeIso p r

def pointBasisEquiv (M : ModuleCat.{u} K) (r : ℕ) (b : Basis (Fin r) K M) :
    PointModule K f p M ≃ₗ[K] (Fin r → K) :=
  (moduleSpecΓFunctor.mapIso (pointBasisIso K f p M r b)).toLinearEquiv.trans (freeCoordinates K r)

theorem pointBasisEquiv_section (M : ModuleCat.{u} K) (r : ℕ) (b : Basis (Fin r) K M) (m : M) :
    pointBasisEquiv K f p M r b (pointConstantSection K f p hp M m) = b.equivFun m := by
  ext i
  change (Scheme.ΓSpecIso (.of K)).hom
    (freeSectionCoordinates (Spec (.of K)) r
      ((pullbackFreeIso p r).hom.app ⊤
        (((Scheme.Modules.pullback p).map (basisIso (.of K) f M r b).hom).app ⊤
          (pullbackGlobalSections p (constantObj (.of K) f M)
            (constantSection (.of K) f M m)))) i) = _
  rw [pullback_map_app_pullbackGlobalSections, freeCoordinates_pullback]
  have hc : freeSectionCoordinates X r
      ((basisIso (.of K) f M r b).hom.app ⊤ (constantSection (.of K) f M m)) i =
      MukaiConstantFreeBasis.baseScalar (.of K) f (b.equivFun m i) := by
    have h := constantBasisIso_coordinates (.of K) f M r (b.reindex Equiv.ulift.symm) m i
    simpa only [basisIso, constantSection, Basis.repr_reindex_apply, Equiv.symm_symm,
      Equiv.ulift_apply, Basis.equivFun_apply] using h
  rw [hc, fieldPoint_baseScalar K f p hp, Iso.inv_hom_id_apply]

theorem pointConstantSection_bijective (M : ModuleCat.{u} K) [Module.Finite K M] :
    Function.Bijective (pointConstantSection K f p hp M) := by
  let b := Module.finBasis K M
  constructor
  · intro m n hmn
    apply b.equivFun.injective
    simpa only [pointBasisEquiv_section] using
      congrArg (pointBasisEquiv K f p M (finrank K M) b) hmn
  · intro s
    refine ⟨b.equivFun.symm (pointBasisEquiv K f p M (finrank K M) b s), ?_⟩
    apply (pointBasisEquiv K f p M (finrank K M) b).injective
    rw [pointBasisEquiv_section, LinearEquiv.apply_symm_apply]

def pointConstantEquiv (M : ModuleCat.{u} K) [Module.Finite K M] :
    M ≃ₗ[K] PointModule K f p M :=
  LinearEquiv.ofBijective (pointConstantSection K f p hp M)
    (pointConstantSection_bijective K f p hp M)

theorem pointConstantSection_naturality {M N : ModuleCat.{u} K} (a : M ⟶ N) (m : M) :
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map (constantMap (.of K) f a))).hom
      (pointConstantSection K f p hp M m) = pointConstantSection K f p hp N (a.hom m) := by
  change ((Scheme.Modules.pullback p).map (constantMap (.of K) f a)).app ⊤
    (pullbackGlobalSections p (constantObj (.of K) f M) (constantSection (.of K) f M m)) = _
  rw [pullback_map_app_pullbackGlobalSections, constantMap_section]
  rfl

theorem pointConstantEquiv_naturality {M N : ModuleCat.{u} K}
    [Module.Finite K M] [Module.Finite K N] (a : M ⟶ N) :
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map (constantMap (.of K) f a))).hom.comp
      (pointConstantEquiv K f p hp M).toLinearMap =
      (pointConstantEquiv K f p hp N).toLinearMap.comp a.hom := by
  ext m
  exact pointConstantSection_naturality K f p hp a m

end M9Native.MukaiConstantPointSections
