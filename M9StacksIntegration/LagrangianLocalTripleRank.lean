module

public import M9StacksIntegration.LagrangianTripleNaturality
public import M9StacksIntegration.LagrangianLocalTripleDeterminant
public import M9StacksIntegration.FieldPointOpenValues

/-! Actual local triple matrices compute the original evaluation rank
at every original field-valued point. All quotient, scalar, point-lift,
and residue-rank comparisons are derived from the original native maps. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianLocalTripleRank

open SpecFieldStalkSections LagrangianMatrixChart
open LagrangianUniversalSections LagrangianUniversalTriples LagrangianLocalTripleDeterminant

variable (k : Type u) [Field k] [CharZero k]
  (U : (LagrangianGrassmannian.space k).affineOpens)
  (e : bundle k (U : (LagrangianGrassmannian.space k).Opens).ι ≅ freeOn (U : Scheme.{u}) 3)
  (s : Fin 3 → (Fin 6 → k))
  (K : Type u) [Field K] {X : Scheme.{u}} (g : X ⟶ LagrangianGrassmannian.space k)
  (p : Spec (.of K) ⟶ X)
  (hp : (p ≫ g).base (point K) ∈ (U : (LagrangianGrassmannian.space k).Opens))

/-- Every genuine local evaluated determinant matrix has exactly the original native triple rank. -/
theorem rank_localMatrix_eq_mapRankAt :
    ((localMatrix k U e s).map
      (FieldPointLocalDerivation.valueOnRingHom K (p ≫ g)
        (U : (LagrangianGrassmannian.space k).Opens) hp)).rank =
      MukaiSemiIrreducible.mapRankAt
        (evaluation k (g ≫ LagrangianGrassmannian.projection k) g s) (p (point K)) := by
  let V : (LagrangianGrassmannian.space k).Opens := U
  let q := FieldPointOpenValues.liftToOpen K (p ≫ g) V hp
  let a := evaluation k (V.ι ≫ LagrangianGrassmannian.projection k) V.ι s ≫ e.hom
  have hm : (localMatrix k U e s).map
      (FieldPointLocalDerivation.valueOnRingHom K (p ≫ g) V hp) =
      (Stacks.FreeSheafMatrix.toMatrix a).map (LagrangianFieldJetCoefficients.pointValue K q) := by
    ext i j
    exact FieldPointOpenValues.valueOn_topIso K (p ≫ g) V hp
      (Stacks.FreeSheafMatrix.toMatrix a i j)
  rw [hm,← SheafMapPullbackRank.mapRankAt_eq_rank_pointValue K q 3 a]
  have he := FieldPointMapRankConsequences.mapRankAt_iso_conjugate
    (evaluation k (V.ι ≫ LagrangianGrassmannian.projection k) V.ι s) (Iso.refl _) e (q (point K))
  change MukaiSemiIrreducible.mapRankAt (𝟙 _ ≫ a) (q (point K)) = _ at he
  rw [Category.id_comp] at he
  refine he.trans ((LagrangianTripleNaturality.evaluation_mapRankAt_eq_ambient k V.ι s
    (q (point K))).trans ?_)
  have hq : V.ι (q (point K)) = g (p (point K)) := by
    have h := congrArg (fun t => t (point K)) (FieldPointOpenValues.liftToOpen_fac K (p ≫ g) V hp)
    exact h
  rw [hq]
  exact (LagrangianTripleNaturality.evaluation_mapRankAt_eq_ambient k g s (p (point K))).symm

end M9Native.LagrangianLocalTripleRank
