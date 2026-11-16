module

public import M9StacksIntegration.FreeTwoPairIncidence
public import M9StacksIntegration.PullbackQuotientSquare
public import M9StacksIntegration.TensorProductPullbackFrame
public import M9StacksIntegration.ClosedIdealPullbackPaste
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChangeTwist

/-! Base change of the original free-two coefficient incidence,
including its original tautological quotient, its full ideal sheaf,
and its original base projection. No equation comparison is assumed. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.presheaf AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
namespace M9Native.FreeTwoPairIncidenceBaseChange
open LagrangianMatrixChart FreeTwoProjectiveCharts LinearIncidenceTensorCoordinates

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

abbrev sourceFreeIso : freeOn Y 2 ≅ (Scheme.Modules.pullback g).obj (freeOn X 2) :=
  (AlgebraicGeometry.Grassmannian.pullbackFreeIso g 2).symm

abbrev bundleData := Stacks.Chow.bundleBaseChange g (freeOn X 2) (freeOn Y 2) (sourceFreeIso g)

def bundleMap : projectiveBundleSpace Y ⟶ projectiveBundleSpace X :=
  (bundleData g).iso.hom ≫ pullback.snd g (projectiveBundleProjection X)

theorem bundleMap_eq : bundleMap g =
    Stacks.Chow.bundleBaseChangeHom g (freeOn X 2) (freeOn Y 2) (sourceFreeIso g) :=
  Stacks.Chow.bundleBaseChangeIso_hom_snd g (freeOn X 2) (freeOn Y 2) (sourceFreeIso g)

theorem bundleSquare : IsPullback (projectiveBundleProjection Y) (bundleMap g)
    g (projectiveBundleProjection X) := by
  rw [bundleMap_eq]
  exact Stacks.Chow.isPullback_bundleBaseChangeHom g (freeOn X 2) (freeOn Y 2) (sourceFreeIso g)

theorem bundleComm : bundleMap g ≫ projectiveBundleProjection X =
    projectiveBundleProjection Y ≫ g :=
  Stacks.Chow.snd_bundleProj_of_hom_fst g (freeOn X 2) (freeOn Y 2)
    (bundleData g).iso (bundleData g).iso_hom_fst

abbrev lineIso : (Scheme.Modules.pullback (bundleMap g)).obj (tautologicalLine X) ≅
    tautologicalLine Y := (bundleData g).twistIso

private theorem tautological_square :
    (PullbackQuotientSquare.sourceIso g (projectiveBundleProjection X)
      (projectiveBundleProjection Y) (bundleMap g) (bundleComm g) (freeOn X 2)).hom ≫
      (Scheme.Modules.pullback (bundleMap g)).map (Stacks.Chow.bundleTautological (freeOn X 2)) ≫
      (lineIso g).hom =
    (Scheme.Modules.pullback (projectiveBundleProjection Y)).map (sourceFreeIso g).inv ≫
      Stacks.Chow.bundleTautological (freeOn Y 2) :=
  (bundleData g).twistIso_spec

theorem coordinate_eq (k : Fin 2) : (lineIso g).hom.app ⊤
    (pullbackGlobalSections (bundleMap g) (tautologicalLine X) (tautCoordinate X k)) =
    tautCoordinate Y k := by
  have h := PullbackQuotientSquare.quotient_section g (projectiveBundleProjection X)
    (projectiveBundleProjection Y) (bundleMap g) (bundleComm g) (freeOn X 2) (freeOn Y 2)
    (sourceFreeIso g).inv (tautologicalLine X) (tautologicalLine Y)
    (Stacks.Chow.bundleTautological (freeOn X 2)) (Stacks.Chow.bundleTautological (freeOn Y 2))
    (lineIso g) (tautological_square g) (freeBasisSection X 2 k)
  have hb : (sourceFreeIso g).inv.app ⊤
      (pullbackGlobalSections g (freeOn X 2) (freeBasisSection X 2 k)) = freeBasisSection Y 2 k :=
    FiniteFreeBasisPullback.freeBasisSection_pullback g 2 k
  exact h.trans (congrArg (fun z => (Stacks.Chow.bundleTautological (freeOn Y 2)).app ⊤
    (pullbackGlobalSections (projectiveBundleProjection Y) (freeOn Y 2) z)) hb)

variable (F : X.Modules) (F' : Y.Modules) (hF : F' ≅ (Scheme.Modules.pullback g).obj F)

def targetIso : (Scheme.Modules.pullback (bundleMap g)).obj (FreeTwoPairIncidence.pulledTarget X F) ≅
    FreeTwoPairIncidence.pulledTarget Y F' :=
  (PullbackQuotientSquare.sourceIso g (projectiveBundleProjection X)
    (projectiveBundleProjection Y) (bundleMap g) (bundleComm g) F).symm ≪≫
    (Scheme.Modules.pullback (projectiveBundleProjection Y)).mapIso hF.symm

theorem targetIso_apply (s : Γ(F,⊤)) : (targetIso g F F' hF).hom.app ⊤
    (pullbackGlobalSections (bundleMap g) (FreeTwoPairIncidence.pulledTarget X F)
      (pullbackGlobalSections (projectiveBundleProjection X) F s)) =
    pullbackGlobalSections (projectiveBundleProjection Y) F'
      (hF.inv.app ⊤ (pullbackGlobalSections g F s)) := by
  change ((Scheme.Modules.pullback (projectiveBundleProjection Y)).map hF.inv).app ⊤
    ((PullbackQuotientSquare.sourceIso g (projectiveBundleProjection X)
      (projectiveBundleProjection Y) (bundleMap g) (bundleComm g) F).inv.app ⊤
      (pullbackGlobalSections (bundleMap g) (FreeTwoPairIncidence.pulledTarget X F)
        (pullbackGlobalSections (projectiveBundleProjection X) F s))) = _
  rw [PullbackQuotientSquare.sourceIso_inv_apply,
    SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections]

def equationIso : (Scheme.Modules.pullback (bundleMap g)).obj (FreeTwoPairIncidence.equationBundle X F) ≅
    FreeTwoPairIncidence.equationBundle Y F' :=
  TensorProductPullbackFrame.frame (bundleMap g) (FreeTwoPairIncidence.pulledTarget X F)
    (tautologicalLine X) (FreeTwoPairIncidence.pulledTarget Y F') (tautologicalLine Y)
    (targetIso g F F' hF) (lineIso g)

def sections (s : Fin 2 → Γ(F,⊤)) : Fin 2 → Γ(F',⊤) :=
  fun k => hF.inv.app ⊤ (pullbackGlobalSections g F (s k))

theorem equationIso_apply (s : Fin 2 → Γ(F,⊤)) : (equationIso g F F' hF).hom.app ⊤
    (pullbackGlobalSections (bundleMap g) (FreeTwoPairIncidence.equationBundle X F)
      (FreeTwoPairIncidence.equationSection X F s)) =
    FreeTwoPairIncidence.equationSection Y F' (sections g F F' hF s) := by
  simp only [FreeTwoPairIncidence.equationSection,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have h := TensorProductPullbackFrame.frame_apply (bundleMap g)
    (FreeTwoPairIncidence.pulledTarget X F) (tautologicalLine X)
    (FreeTwoPairIncidence.pulledTarget Y F') (tautologicalLine Y)
    (targetIso g F F' hF) (lineIso g)
    (pullbackGlobalSections (projectiveBundleProjection X) F (s k)) (tautCoordinate X k)
  rw [targetIso_apply,coordinate_eq] at h
  exact h

variable (r : ℕ) [hFr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r]
  [hFpr : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F' r]

include r hFr hFpr in
theorem ideal_eq (s : Fin 2 → Γ(F,⊤)) :
    FreeTwoPairIncidence.ideal Y F' (sections g F F' hF s) =
      (FreeTwoPairIncidence.ideal X F s).comap (bundleMap g) := by
  letI := FreeTwoPairIncidence.equationBundle_rank X F r
  letI := FreeTwoPairIncidence.equationBundle_rank Y F' r
  letI := isFiniteLocallyFreeOfRank_pullback (bundleMap g) (FreeTwoPairIncidence.equationBundle X F) r
  rw [FreeTwoPairIncidence.ideal,← equationIso_apply g F F' hF s]
  exact (LagrangianMatrixChart.sectionZeroIdeal_eq_of_iso r (equationIso g F F' hF)
    (pullbackGlobalSections (bundleMap g) (FreeTwoPairIncidence.equationBundle X F)
      (FreeTwoPairIncidence.equationSection X F s))).symm.trans
        (SectionZeroIdealFactorization.sectionZeroIdeal_pullback (bundleMap g)
          (FreeTwoPairIncidence.equationBundle X F) r (FreeTwoPairIncidence.equationSection X F s))

def baseChangeIso (s : Fin 2 → Γ(F,⊤)) :
    FreeTwoPairIncidence.space Y F' (sections g F F' hF s) ≅
      pullback g (FreeTwoPairIncidence.toBase X F s) :=
  ClosedIdealPullbackPaste.zeroIsoPullback (projectiveBundleProjection X)
    (projectiveBundleProjection Y) (bundleMap g) g (bundleSquare g)
    (FreeTwoPairIncidence.ideal X F s) (FreeTwoPairIncidence.ideal Y F' (sections g F F' hF s))
    (ideal_eq g F F' hF r s)

@[reassoc]
theorem baseChangeIso_hom_fst (s : Fin 2 → Γ(F,⊤)) :
    (baseChangeIso g F F' hF r s).hom ≫ pullback.fst g (FreeTwoPairIncidence.toBase X F s) =
      FreeTwoPairIncidence.toBase Y F' (sections g F F' hF s) :=
  ClosedIdealPullbackPaste.zeroIsoPullback_hom_fst (projectiveBundleProjection X)
    (projectiveBundleProjection Y) (bundleMap g) g (bundleSquare g)
    (FreeTwoPairIncidence.ideal X F s) (FreeTwoPairIncidence.ideal Y F' (sections g F F' hF s))
    (ideal_eq g F F' hF r s)

end M9Native.FreeTwoPairIncidenceBaseChange
