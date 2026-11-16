module

public import M9StacksIntegration.LagrangianIncidenceRankDrop
public import M9StacksIntegration.LagrangianBetaRankDrop

/-! The actual C-only incidence has an actual map to the full native
beta zero scheme. It is constructed from the original rank-drop map
and the full native ideal comparison; no isomorphism is assumed. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace M9Native.LagrangianCurveIncidenceBetaFactor
open LagrangianOrderedFibre LagrangianRankTwoSubsystemBundles LagrangianBetaRankDrop
variable (K : Type u) [Field K] [CharZero K]
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  [IsIntegral (model K M hM)]
  [SmoothOfRelativeDimension 1 (modelProjection K M hM)]
  (s : Fin 3 → (Fin 6 → K))
  (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
  (e : Fin 2 ↪ Fin 3)

abbrev curveIncidence := pullback (modelInclusion K M hM)
  (LagrangianArbitraryPlaneIncidence.incidenceToLG K (s ∘ e))

abbrev nativeBetaIdeal := Stacks.Chow.zeroSchemeOfSection (model K M hM)
  (beta K M hM s) (betaSection K M hM s hr e)

def nativeBetaRankDropIso : (nativeBetaIdeal K M hM s hr e).subscheme ≅
    pullback (modelInclusion K M hM)
      (LagrangianArbitraryPlaneIncidence.rankDropInclusion K (s ∘ e)) :=
  eqToIso (congrArg (fun I : (model K M hM).IdealSheafData => I.subscheme)
    (nativeBetaZeroIdeal_eq_rankDrop_comap K M hM s hr e)) ≪≫
    (LagrangianArbitraryPlaneIncidence.rankDropIdeal K (s ∘ e)).comapIso (modelInclusion K M hM)

@[reassoc]
theorem nativeBetaRankDropIso_hom_fst : (nativeBetaRankDropIso K M hM s hr e).hom ≫
    pullback.fst _ _ = (nativeBetaIdeal K M hM s hr e).subschemeι := by
  rw [nativeBetaRankDropIso,Iso.trans_hom,Category.assoc,Scheme.IdealSheafData.comapIso_hom_fst]
  exact LagrangianMatrixChart.eqToIso_subscheme_ι _ _
    (nativeBetaZeroIdeal_eq_rankDrop_comap K M hM s hr e)

@[reassoc]
theorem nativeBetaRankDropIso_inv_inclusion : (nativeBetaRankDropIso K M hM s hr e).inv ≫
    (nativeBetaIdeal K M hM s hr e).subschemeι = pullback.fst _ _ := by
  apply (cancel_epi (nativeBetaRankDropIso K M hM s hr e).hom).mp
  rw [Iso.hom_inv_id_assoc,nativeBetaRankDropIso_hom_fst]

def toRankDropPullback : curveIncidence K M hM s e ⟶
    pullback (modelInclusion K M hM)
      (LagrangianArbitraryPlaneIncidence.rankDropInclusion K (s ∘ e)) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫
    LagrangianIncidenceRankDrop.incidenceToRankDrop K (s ∘ e)) (by
      rw [Category.assoc,LagrangianIncidenceRankDrop.incidenceToRankDrop_toLG]
      exact pullback.condition)

def curveIncidenceToBeta : curveIncidence K M hM s e ⟶ (nativeBetaIdeal K M hM s hr e).subscheme :=
  toRankDropPullback K M hM s e ≫ (nativeBetaRankDropIso K M hM s hr e).inv

@[reassoc]
theorem curveIncidenceToBeta_inclusion : curveIncidenceToBeta K M hM s hr e ≫
    (nativeBetaIdeal K M hM s hr e).subschemeι = pullback.fst _ _ := by
  rw [curveIncidenceToBeta,Category.assoc,nativeBetaRankDropIso_inv_inclusion]
  exact pullback.lift_fst _ _ _

end M9Native.LagrangianCurveIncidenceBetaFactor
