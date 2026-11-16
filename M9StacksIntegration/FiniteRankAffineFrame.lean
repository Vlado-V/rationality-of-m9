module

public import M9StacksIntegration.SectionZeroEvaluation
public import M9StacksIntegration.LagrangianUniversalSections
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictFree

/-!
# Actual affine frames from the original finite locally free rank data

The original native generating cover supplies an isomorphism over one
cover member. It is restricted to an actual affine neighbourhood and
reindexed by the original rank data. The canonical restriction/pullback
comparison gives an actual frame of the original scheme pullback.
No free-frame or stalk-basis premise is introduced.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.FiniteRankAffineFrame

open LagrangianMatrixChart

/-- Native free sheaves reindex through the literal coproduct equivalence. -/
def freeIndexIso {X : Scheme.{u}} {I J : Type u} (e : I ≃ J) :
    (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules) ≅
      SheafOfModules.free (R := X.ringCatSheaf) J :=
  Sigma.reindex e (fun _ : J => SheafOfModules.unit X.ringCatSheaf)

/-- Every original point has an actual affine pullback frame of the proved native rank. -/
theorem exists_affine_pullback_frame {X : Scheme.{u}} (E : X.Modules) (r : ℕ)
    [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r]
    {U : X.Opens} {x : X} (hx : x ∈ U) :
    ∃ (V : X.affineOpens), x ∈ (V : X.Opens) ∧ (V : X.Opens) ≤ U ∧
      Nonempty ((Scheme.Modules.pullback (V : X.Opens).ι).obj E ≅
        freeOn (V : Scheme.{u}) r) := by
  classical
  obtain ⟨q, hq, hrank⟩ := hE.exists_isFiniteLocallyFreeOfRankData
  obtain ⟨i, hxi⟩ := ((Opens.coversTop_iff (X : Type u) q.X).mp q.coversTop).exists_mem x
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ U ⊓ q.X i from ⟨hx, hxi⟩) (U ⊓ q.X i).isOpen
  let W : X.Opens := q.X i
  let I := (q.generators i).I
  let eW : E.restrict W.ι ≅ SheafOfModules.free (R := W.toScheme.ringCatSheaf) I :=
    LocallyFreeRank.restrictIsoFreeOfGeneratingSections E W (q.generators i) (hq.isIso i)
  let eV : E.restrict (show X.Opens from V).ι ≅
      SheafOfModules.free (R := (show X.Opens from V).toScheme.ringCatSheaf) I :=
    Scheme.Modules.restrictFreeOfLE (show V ≤ W from fun y hy => (hVU hy).2) E I eW
  let eI : I ≃ ULift.{u} (Fin r) := (hrank i).some.trans Equiv.ulift.symm
  exact ⟨⟨V,hV⟩, hxV, (fun y hy => (hVU hy).1),
    ⟨((Scheme.Modules.restrictFunctorIsoPullback (show X.Opens from V).ι).app E).symm ≪≫
      eV ≪≫ freeIndexIso eI⟩⟩

/-- The actual original universal quotient therefore has such a frame at every actual LG point. -/
theorem exists_affine_lagrangian_quotient_frame
    (K : Type u) [Field K] (x : LagrangianGrassmannian.space K) :
    ∃ (V : (LagrangianGrassmannian.space K).affineOpens),
      x ∈ (V : (LagrangianGrassmannian.space K).Opens) ∧
      Nonempty (LagrangianUniversalSections.bundle K (V : (LagrangianGrassmannian.space K).Opens).ι ≅
        freeOn (V : Scheme.{u}) 3) := by
  letI := (LagrangianPluckerQuotient.quotientOnLG K).finiteLocallyFree
  obtain ⟨V,hxV,_,hV⟩ := exists_affine_pullback_frame
    (LagrangianPluckerQuotient.quotientOnLG K).target 3 (x := x) (U := ⊤) (by simp)
  exact ⟨V,hxV,hV⟩

end M9Native.FiniteRankAffineFrame
