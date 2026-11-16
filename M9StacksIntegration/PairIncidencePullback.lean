module

public import M9StacksIntegration.PairIncidenceUnitMorphism
public import M9StacksIntegration.PullbackQuotientSquare
public import M9StacksIntegration.TensorProductPullbackFrame
public import M9StacksIntegration.ClosedIdealPullbackPaste

/-! Direct base change from an original native pairing incidence to
an actual tensor incidence. The full source/target schemes, modules
and tautological quotients are retained in one genuine datum. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.presheaf AlgebraicGeometry.SheafedSpace.sheaf
  Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
namespace M9Native.PairIncidencePullback
open LagrangianMatrixChart LinearIncidenceTensorCoordinates

structure Datum where
  X : Scheme.{u}
  Y : Scheme.{u}
  P : Scheme.{u}
  Q : Scheme.{u}
  g : Y ⟶ X
  p : P ⟶ X
  q : Q ⟶ Y
  b : Q ⟶ P
  cartesian : IsPullback q b g p
  E : X.Modules
  E' : Y.Modules
  eE : E' ≅ (Scheme.Modules.pullback g).obj E
  L : P.Modules
  L' : Q.Modules
  tau : (Scheme.Modules.pullback p).obj (freeOn X 2) ⟶ L
  tau' : (Scheme.Modules.pullback q).obj (freeOn Y 2) ⟶ L'
  eL : (Scheme.Modules.pullback b).obj L ≅ L'
  tau_spec :
    (PullbackQuotientSquare.sourceIso g p q b cartesian.w.symm (freeOn X 2)).hom ≫
      (Scheme.Modules.pullback b).map tau ≫ eL.hom =
    (Scheme.Modules.pullback q).map (AlgebraicGeometry.Grassmannian.pullbackFreeIso g 2).hom ≫ tau'

variable (d : Datum.{u})

abbrev sourceTarget := (Scheme.Modules.pullback d.p).obj d.E
abbrev targetTarget := (Scheme.Modules.pullback d.q).obj d.E'
abbrev sourceBundle := tensorObj d.P (sourceTarget d) d.L
abbrev targetBundle := tensorObj d.Q (targetTarget d) d.L'

def sourceEquation (s : Fin 2 → Γ(d.E,⊤)) : Γ(sourceBundle d,⊤) :=
  ∑ k : Fin 2, PairIncidenceUnitMorphism.pairingTerm d.p d.E d.L d.tau s k

def targetSections (s : Fin 2 → Γ(d.E,⊤)) : Fin 2 → Γ(d.E',⊤) :=
  fun k => d.eE.inv.app ⊤ (pullbackGlobalSections d.g d.E (s k))

def targetEquation (s : Fin 2 → Γ(d.E,⊤)) : Γ(targetBundle d,⊤) :=
  ∑ k : Fin 2, PairIncidenceUnitMorphism.tensorTerm d.q d.E' d.L' d.tau' (targetSections d s) k

theorem coordinate_eq (k : Fin 2) : d.eL.hom.app ⊤
    (pullbackGlobalSections d.b d.L (PairTensorUnitMorphism.coordinate d.p d.L d.tau k)) =
    PairTensorUnitMorphism.coordinate d.q d.L' d.tau' k := by
  have h := PullbackQuotientSquare.quotient_section d.g d.p d.q d.b d.cartesian.w.symm
    (freeOn d.X 2) (freeOn d.Y 2) (AlgebraicGeometry.Grassmannian.pullbackFreeIso d.g 2).hom
    d.L d.L' d.tau d.tau' d.eL d.tau_spec (freeBasisSection d.X 2 k)
  exact h.trans (congrArg (fun z => d.tau'.app ⊤ (pullbackGlobalSections d.q (freeOn d.Y 2) z))
    (FiniteFreeBasisPullback.freeBasisSection_pullback d.g 2 k))

def vectorIso : (Scheme.Modules.pullback d.b).obj (sourceTarget d) ≅ targetTarget d :=
  (PullbackQuotientSquare.sourceIso d.g d.p d.q d.b d.cartesian.w.symm d.E).symm ≪≫
    (Scheme.Modules.pullback d.q).mapIso d.eE.symm

theorem vectorIso_apply (s : Γ(d.E,⊤)) : (vectorIso d).hom.app ⊤
    (pullbackGlobalSections d.b (sourceTarget d) (pullbackGlobalSections d.p d.E s)) =
    pullbackGlobalSections d.q d.E' (d.eE.inv.app ⊤ (pullbackGlobalSections d.g d.E s)) := by
  change ((Scheme.Modules.pullback d.q).map d.eE.inv).app ⊤
    ((PullbackQuotientSquare.sourceIso d.g d.p d.q d.b d.cartesian.w.symm d.E).inv.app ⊤
      (pullbackGlobalSections d.b (sourceTarget d) (pullbackGlobalSections d.p d.E s))) = _
  rw [PullbackQuotientSquare.sourceIso_inv_apply,
    SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections]

def equationIso : (Scheme.Modules.pullback d.b).obj (sourceBundle d) ≅ targetBundle d :=
  TensorProductPullbackFrame.frame d.b (sourceTarget d) d.L (targetTarget d) d.L' (vectorIso d) d.eL

private theorem frame_pairing_apply {A B : Scheme.{u}} (f : A ⟶ B)
    (E L : B.Modules) (E' L' : A.Modules)
    (eE : (Scheme.Modules.pullback f).obj E ≅ E') (eL : (Scheme.Modules.pullback f).obj L ≅ L')
    (s : Γ(E,⊤)) (t : Γ(L,⊤)) :
    (TensorProductPullbackFrame.frame f E L E' L' eE eL).hom.app ⊤
      (pullbackGlobalSections f (tensorObj B E L)
        (Stacks.SheafOfModules.pairingApp (Stacks.SheafOfModules.Tensor.ringSheaf B.sheaf)
          (Stacks.SheafOfModules.tensorSectionPairing (O := B.sheaf) E L) (op ⊤) s t)) =
    tensorTop A E' L' (eE.hom.app ⊤ (pullbackGlobalSections f E s))
      (eL.hom.app ⊤ (pullbackGlobalSections f L t)) := by
  exact (congrArg (fun z =>
    (TensorProductPullbackFrame.frame f E L E' L' eE eL).hom.app ⊤
      (pullbackGlobalSections f (tensorObj B E L) z))
    (TensorPairingTopComparison.pairing_eq_tensorTop B E L s t)).trans
      (TensorProductPullbackFrame.frame_apply f E L E' L' eE eL s t)

theorem equationIso_apply (s : Fin 2 → Γ(d.E,⊤)) : (equationIso d).hom.app ⊤
    (pullbackGlobalSections d.b (sourceBundle d) (sourceEquation d s)) = targetEquation d s := by
  simp only [sourceEquation,targetEquation,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have h := frame_pairing_apply d.b (sourceTarget d) d.L (targetTarget d) d.L' (vectorIso d) d.eL
    (pullbackGlobalSections d.p d.E (s k)) (PairTensorUnitMorphism.coordinate d.p d.L d.tau k)
  rw [vectorIso_apply,coordinate_eq] at h
  exact h

def sourceIdeal (s : Fin 2 → Γ(d.E,⊤)) : d.P.IdealSheafData :=
  SectionZeroIdealFactorization.sectionZeroIdeal d.P (sourceBundle d) (sourceEquation d s)

def targetIdeal (s : Fin 2 → Γ(d.E,⊤)) : d.Q.IdealSheafData :=
  SectionZeroIdealFactorization.sectionZeroIdeal d.Q (targetBundle d) (targetEquation d s)

private theorem tensor_rank (X : Scheme.{u}) (E L : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tensorObj X E L) r := by
  have h : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tensorObj X E L) (r*1) :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X E L r 1
  exact (Nat.mul_one r) ▸ h

theorem ideal_eq (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} d.E r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} d.E' r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} d.L 1]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} d.L' 1]
    (s : Fin 2 → Γ(d.E,⊤)) : targetIdeal d s = (sourceIdeal d s).comap d.b := by
  letI := isFiniteLocallyFreeOfRank_pullback d.p d.E r
  letI := isFiniteLocallyFreeOfRank_pullback d.q d.E' r
  letI := tensor_rank d.P (sourceTarget d) d.L r
  letI := tensor_rank d.Q (targetTarget d) d.L' r
  letI := isFiniteLocallyFreeOfRank_pullback d.b (sourceBundle d) r
  rw [targetIdeal,← equationIso_apply d s]
  exact (LagrangianMatrixChart.sectionZeroIdeal_eq_of_iso r (equationIso d)
    (pullbackGlobalSections d.b (sourceBundle d) (sourceEquation d s))).symm.trans
      (SectionZeroIdealFactorization.sectionZeroIdeal_pullback d.b (sourceBundle d) r (sourceEquation d s))

end M9Native.PairIncidencePullback
