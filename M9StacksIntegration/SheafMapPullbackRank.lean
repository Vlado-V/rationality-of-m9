module

public import M9StacksIntegration.FieldPointMapRankConsequences
public import M9StacksIntegration.PrimitiveFreeMatrixPullback
public import M9StacksIntegration.LagrangianFieldJetCoefficients

/-! Native map rank is preserved by actual scheme pullback at its actual
point. Actual free-sheaf matrices at a field point have their literal
point-value rank. Neither statement assumes a fibre comparison. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.SheafMapPullbackRank

open SpecFieldStalkSections LagrangianMatrixChart AlgebraicGeometry.Grassmannian

/-- The actual original map rank after any actual scheme pullback is the rank at the image point. -/
theorem mapRankAt_pullback {X Y : Scheme.{u}} (g : Y ⟶ X) {A B : X.Modules}
    (a : A ⟶ B) (y : Y) :
    MukaiSemiIrreducible.mapRankAt ((Scheme.Modules.pullback g).map a) y =
      MukaiSemiIrreducible.mapRankAt a (g y) := by
  let K := Y.residueField y
  let p : Spec (.of K) ⟶ Y := Y.fromSpecResidueField y
  have hp : p (point K) = y := Scheme.fromSpecResidueField_apply y _
  let eA := (Scheme.Modules.pullbackComp p g).app A
  let eB := (Scheme.Modules.pullbackComp p g).app B
  have hn : eA.inv ≫ (Scheme.Modules.pullback p).map ((Scheme.Modules.pullback g).map a) ≫
      eB.hom = (Scheme.Modules.pullback (p ≫ g)).map a := by
    have h := congrArg (fun t => eA.inv ≫ t) ((Scheme.Modules.pullbackComp p g).hom.naturality a)
    change eA.inv ≫ (Scheme.Modules.pullback p).map ((Scheme.Modules.pullback g).map a) ≫
      eB.hom = eA.inv ≫ eA.hom ≫ (Scheme.Modules.pullback (p ≫ g)).map a at h
    simpa only [Iso.inv_hom_id_assoc] using h
  calc
    _ = MukaiSemiIrreducible.mapRankAt
        ((Scheme.Modules.pullback p).map ((Scheme.Modules.pullback g).map a)) (point K) := by
      exact (congrArg
        (fun z => MukaiSemiIrreducible.mapRankAt ((Scheme.Modules.pullback g).map a) z) hp).symm.trans
        (FieldPointMapRankConsequences.mapRankAt_pullback K
          ((Scheme.Modules.pullback g).map a) p).symm
    _ = MukaiSemiIrreducible.mapRankAt ((Scheme.Modules.pullback (p ≫ g)).map a) (point K) := by
      have h := FieldPointMapRankConsequences.mapRankAt_iso_conjugate
        ((Scheme.Modules.pullback p).map ((Scheme.Modules.pullback g).map a)) eA.symm eB (point K)
      change MukaiSemiIrreducible.mapRankAt
        (eA.inv ≫ (Scheme.Modules.pullback p).map ((Scheme.Modules.pullback g).map a) ≫ eB.hom)
          (point K) = _ at h
      rw [hn] at h
      exact h.symm
    _ = _ := by
      simpa only [Scheme.Hom.comp_apply,hp] using
        FieldPointMapRankConsequences.mapRankAt_pullback K a (p ≫ g)

/-- Literal native free-sheaf matrices have their actual field-point matrix rank. -/
theorem mapRankAt_eq_rank_pointValue (K : Type u) [Field K] {X : Scheme.{u}}
    (p : Spec (.of K) ⟶ X) (n : ℕ) (a : freeOn X n ⟶ freeOn X n) :
    MukaiSemiIrreducible.mapRankAt a (p (point K)) =
      ((Stacks.FreeSheafMatrix.toMatrix a).map (LagrangianFieldJetCoefficients.pointValue K p)).rank := by
  let M := (Stacks.FreeSheafMatrix.toMatrix a).map (LagrangianFieldJetCoefficients.pointValue K p)
  have hm : (pullbackFreeIso p n).inv ≫ (Scheme.Modules.pullback p).map a ≫
      (pullbackFreeIso p n).hom =
        Stacks.FreeSheafMatrix.ofMatrix (M.map (Scheme.ΓSpecIso (.of K)).inv.hom) := by
    apply Stacks.FreeSheafMatrix.toMatrix_injective
    rw [Stacks.FreeSheafMatrix.toMatrix_ofMatrix]
    change Stacks.FreeSheafMatrix.toMatrix (PrimitiveFreeMatrixPullback.pulledFreeEnd p n a) = _
    rw [PrimitiveFreeMatrixPullback.pulledFreeEnd_matrix]
    ext i j
    exact ((Scheme.ΓSpecIso (.of K)).hom_inv_id_apply
      (p.appTop (Stacks.FreeSheafMatrix.toMatrix a i j))).symm
  exact FieldPointMapRankConsequences.mapRankAt_of_point_frame K a p
    (pullbackFreeIso p n) M hm

end M9Native.SheafMapPullbackRank
