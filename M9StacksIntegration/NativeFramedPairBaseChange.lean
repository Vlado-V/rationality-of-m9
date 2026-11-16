module

public import M9StacksIntegration.PairIncidencePullbackTerm
public import M9StacksIntegration.FreeTwoPairIncidence
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChangeTwist

/-! Native base change retaining the actual SOURCE coefficient module.
Only its genuine free frame is transported; its projective bundle,
twist and tautological quotient are never replaced by a free-source model. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.presheaf AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
namespace M9Native.NativeFramedPairBaseChange
open LagrangianMatrixChart LinearIncidenceTensorCoordinates FreeTwoProjectiveCharts
variable {X Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules)
  [hN : SheafOfModules.IsFiniteLocallyFree.{u,u,u} N] (eN : N ≅ freeOn X 2)

abbrev sourceFreeIso : freeOn Y 2 ≅ (Scheme.Modules.pullback g).obj N :=
  (AlgebraicGeometry.Grassmannian.pullbackFreeIso g 2).symm ≪≫
    (Scheme.Modules.pullback g).mapIso eN.symm

abbrev bundleData := Stacks.Chow.bundleBaseChange g N (freeOn Y 2) (sourceFreeIso g N eN)

def bundleMap : projectiveBundleSpace Y ⟶ Stacks.Chow.bundle N :=
  (bundleData g N eN).iso.hom ≫ pullback.snd g (Stacks.Chow.bundleProj N)

theorem bundleSquare : IsPullback (projectiveBundleProjection Y) (bundleMap g N eN)
    g (Stacks.Chow.bundleProj N) := by
  change IsPullback _ ((Stacks.Chow.bundleBaseChangeIso g N (freeOn Y 2)
    (sourceFreeIso g N eN)).hom ≫ pullback.snd g (Stacks.Chow.bundleProj N)) _ _
  rw [Stacks.Chow.bundleBaseChangeIso_hom_snd]
  exact Stacks.Chow.isPullback_bundleBaseChangeHom g N (freeOn Y 2) (sourceFreeIso g N eN)

def lineIso : (Scheme.Modules.pullback (bundleMap g N eN)).obj (Stacks.Chow.bundleTwist N) ≅
    tautologicalLine Y := (bundleData g N eN).twistIso

theorem tautological_square :
    (PullbackQuotientSquare.sourceIso g (Stacks.Chow.bundleProj N) (projectiveBundleProjection Y)
      (bundleMap g N eN) (bundleSquare g N eN).w.symm N).hom ≫
      (Scheme.Modules.pullback (bundleMap g N eN)).map (Stacks.Chow.bundleTautological N) ≫
      (lineIso g N eN).hom =
    (Scheme.Modules.pullback (projectiveBundleProjection Y)).map (sourceFreeIso g N eN).inv ≫
      Stacks.Chow.bundleTautological (freeOn Y 2) := (bundleData g N eN).twistIso_spec

theorem sourceFreeIso_inv_basis (k : Fin 2) :
    (sourceFreeIso g N eN).inv.app ⊤
      (pullbackGlobalSections g N (eN.inv.app ⊤ (freeBasisSection X 2 k))) =
    freeBasisSection Y 2 k := by
  change (AlgebraicGeometry.Grassmannian.pullbackFreeIso g 2).hom.app ⊤
    (((Scheme.Modules.pullback g).map eN.hom).app ⊤
      (pullbackGlobalSections g N (eN.inv.app ⊤ (freeBasisSection X 2 k)))) = _
  rw [SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections]
  have h : eN.hom.app ⊤ (eN.inv.app ⊤ (freeBasisSection X 2 k)) = freeBasisSection X 2 k := by
    have h := congrArg (fun f => f.app ⊤ (freeBasisSection X 2 k)) eN.inv_hom_id
    exact h
  rw [h]
  exact FiniteFreeBasisPullback.freeBasisSection_pullback g 2 k

def coordinate (k : Fin 2) : Γ(Stacks.Chow.bundleTwist N,⊤) :=
  (Stacks.Chow.bundleTautological N).app ⊤
    (pullbackGlobalSections (Stacks.Chow.bundleProj N) N
      (eN.inv.app ⊤ (freeBasisSection X 2 k)))

theorem coordinate_apply (k : Fin 2) : (lineIso g N eN).hom.app ⊤
    (pullbackGlobalSections (bundleMap g N eN) (Stacks.Chow.bundleTwist N) (coordinate N eN k)) =
    tautCoordinate Y k := by
  have h := PullbackQuotientSquare.quotient_section g (Stacks.Chow.bundleProj N)
    (projectiveBundleProjection Y) (bundleMap g N eN) (bundleSquare g N eN).w.symm
    N (freeOn Y 2) (sourceFreeIso g N eN).inv (Stacks.Chow.bundleTwist N) (tautologicalLine Y)
    (Stacks.Chow.bundleTautological N) (Stacks.Chow.bundleTautological (freeOn Y 2))
    (lineIso g N eN) (tautological_square g N eN) (eN.inv.app ⊤ (freeBasisSection X 2 k))
  exact h.trans (congrArg (fun z => (Stacks.Chow.bundleTautological (freeOn Y 2)).app ⊤
    (pullbackGlobalSections (projectiveBundleProjection Y) (freeOn Y 2) z))
    (sourceFreeIso_inv_basis g N eN k))

variable (E : X.Modules) (E' : Y.Modules) (eE : E' ≅ (Scheme.Modules.pullback g).obj E)

def vectorIso :
    (Scheme.Modules.pullback (bundleMap g N eN)).obj
      ((Scheme.Modules.pullback (Stacks.Chow.bundleProj N)).obj E) ≅
    (Scheme.Modules.pullback (projectiveBundleProjection Y)).obj E' :=
  (PullbackQuotientSquare.sourceIso g (Stacks.Chow.bundleProj N) (projectiveBundleProjection Y)
    (bundleMap g N eN) (bundleSquare g N eN).w.symm E).symm ≪≫
    (Scheme.Modules.pullback (projectiveBundleProjection Y)).mapIso eE.symm

theorem vectorIso_apply (s : Γ(E,⊤)) : (vectorIso g N eN E E' eE).hom.app ⊤
    (pullbackGlobalSections (bundleMap g N eN)
      ((Scheme.Modules.pullback (Stacks.Chow.bundleProj N)).obj E)
      (pullbackGlobalSections (Stacks.Chow.bundleProj N) E s)) =
    pullbackGlobalSections (projectiveBundleProjection Y) E'
      (eE.inv.app ⊤ (pullbackGlobalSections g E s)) := by
  change ((Scheme.Modules.pullback (projectiveBundleProjection Y)).map eE.inv).app ⊤
    ((PullbackQuotientSquare.sourceIso g (Stacks.Chow.bundleProj N) (projectiveBundleProjection Y)
      (bundleMap g N eN) (bundleSquare g N eN).w.symm E).inv.app ⊤
      (pullbackGlobalSections (bundleMap g N eN)
        ((Scheme.Modules.pullback (Stacks.Chow.bundleProj N)).obj E)
        (pullbackGlobalSections (Stacks.Chow.bundleProj N) E s))) = _
  rw [PullbackQuotientSquare.sourceIso_inv_apply,
    SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections]

end M9Native.NativeFramedPairBaseChange
