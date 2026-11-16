module

public import M9StacksIntegration.SymmetricSquareFreeFrames
public import M9StacksIntegration.LagrangianDualCoefficients
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic

/-! Actual rank-six descent for the native symmetric square of a rank-three bundle. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.LagrangianSymmetricSquareRank

open LagrangianSymmetricSquare SymmetricSquareBundleDeterminant

/-- The actual monomial index follows an actual change of rank-three
index set and preserves its original total degree. -/
def quadraticReindex {I J : Type*} (e : I ≃ J) :
    {d : I →₀ ℕ // d.degree=2} ≃ {d : J →₀ ℕ // d.degree=2} :=
  Equiv.subtypeEquiv (Finsupp.equivCongrLeft e) (by
    intro d
    simp only [Finsupp.equivCongrLeft_apply,Finsupp.equivMapDomain_eq_mapDomain,
      Finsupp.degree_mapDomain])

/-- The literal native symmetric-square sheaf is finite locally free
of rank six. Both its local sheaf frames and their index cardinalities
are derived from the original rank-three frames. -/
theorem symmetricSquare_rank_six {X : Scheme.{u}} (F : X.Modules)
    [hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 3] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (LagrangianDualCoefficients.symmetricSquare F) 6 := by
  classical
  obtain ⟨q,hq,hr⟩ := hF.exists_isFiniteLocallyFreeOfRankData
  let J (i : q.I) := {d : (q.generators i).I →₀ ℕ // d.degree=2}
  have E : ∀ i : q.I,SheafOfModules.free (R := X.ringCatSheaf.over (q.X i)) (J i) ≅
      (LagrangianDualCoefficients.symmetricSquare F).over (q.X i) := fun i => by
    haveI : IsIso (q.generators i).π := hq.isIso i
    exact (symmetricPowerFreeOn F (q.X i) 2 (q.generators i).I
      (asIso (q.generators i).π).symm).symm
  have hcard : ∀ i : q.I,Nonempty (J i ≃ Fin 6) := fun i =>
    ⟨(quadraticReindex (hr i).some).trans quadraticIndexEquiv.symm⟩
  refine ⟨⟨{ I := q.I,
              X := q.X,
              coversTop := q.coversTop,
              generators := fun i => (SheafOfModules.free.generatingSections
                (R := X.ringCatSheaf.over (q.X i)) (J i)).ofEpi (E i).hom },?_,hcard⟩⟩
  constructor
  intro i
  exact AlgebraicGeometry.SheafOfModules.isIso_free_generatingSections_ofEpi_π (J i) (E i)

instance instSymmetricSquareRankSix {X : Scheme.{u}} (F : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 3] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (LagrangianDualCoefficients.symmetricSquare F) 6 :=
  symmetricSquare_rank_six F

theorem symmetricSquare_isQuasicoherent {X : Scheme.{u}} (F : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 3] :
    (LagrangianDualCoefficients.symmetricSquare F).IsQuasicoherent := by
  letI := (symmetricSquare_rank_six F).isFiniteLocallyFree
  exact Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree _

end M9Native.LagrangianSymmetricSquareRank
