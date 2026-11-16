module

public import M9StacksIntegration.MukaiPointLine
public import M9StacksIntegration.MukaiFreePullbackCoordinates
public import M9StacksIntegration.MukaiEvaluationMatrix
public import M9StacksIntegration.LagrangianFixedEquationRows
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.DualBaseChangeNaturality
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DualSectionsInfinitesimal

/-! The canonical dual pullback respects the original actual free
coordinates. Its evaluation formula is the native dual base-change
pairing, including its literal scalar pullback. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  SheafOfModules.unit PresheafOfModules.unit AlgebraicGeometry.SheafedSpace.sheaf

universe u

namespace M9Native.MukaiDualPullbackSections

open MukaiPointLine LagrangianMatrixChart LagrangianFreeDualSections
open MukaiEvaluationMatrix AlgebraicGeometry.Grassmannian
open SectionZeroIdealFactorization

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

theorem app_val_app {A B : X.Modules} (a : A ⟶ B) (U : X.Opens) (s : Γ(A,U)) :
    a.app U s = (a.val.app (op U)).hom s := by
  rfl

theorem evalAt_pullbackGlobalSections (Q : X.Modules)
    (hQ : SheafOfModules.IsFiniteLocallyFree.{u,u,u} Q)
    (a : Γ(dualSheaf Q, ⊤)) (s : Γ(Q, ⊤)) :
    evalAt ((Scheme.Modules.pullback p).obj Q)
      ((Stacks.FundamentalGroup.pullbackDualSheafIso p Q hQ).hom.app ⊤
        (pullbackGlobalSections p (dualSheaf Q) a))
      (pullbackGlobalSections p Q s) = p.appTop (evalAt Q a s) := by
  have h := Stacks.FundamentalGroup.pullbackDualSheafIso_unit_apply p Q hQ ⊤ a s
  rw [LagrangianFixedEquationRows.pullbackGlobalSections_eq_unit,
    LagrangianFixedEquationRows.pullbackGlobalSections_eq_unit]
  simpa only [app_val_app, evalAt, Scheme.Hom.preimage_top, Scheme.Hom.appTop] using h

theorem coordinateInverse_eval (X : Scheme.{u}) (r : ℕ) (i j : Fin r) :
    evalAt (freeOn X r) ((coordinateInverse X r).app ⊤ (freeBasisSection X r i))
      (freeBasisSection X r j) = if j = i then 1 else 0 := by
  unfold coordinateInverse
  rw [LagrangianSectionGeneration.sectionMap_top_basis,
    LagrangianLocalIsotropy.evalAt_functionalSection]
  simpa only [LagrangianMatrixChart.freeSectionCoordinates_apply,
    LagrangianMatrixChart.freeProj_eq_freeProjection, app_val_app, eq_comm] using
      LagrangianFreeMatrixPullback.freeCoordinates_basis X r i j

/-- The actual dual of the canonical free-pullback comparison sends
each original pulled coordinate functional to the original coordinate
functional. This fixes the full comparison, rather than a scalar line. -/
theorem coordinateInverse_pullback (r : ℕ) :
    (pullbackFreeIso p r).inv ≫ (Scheme.Modules.pullback p).map (coordinateInverse X r) ≫
      (Stacks.FundamentalGroup.pullbackDualSheafIso p (freeOn X r)
        (SheafOfModules.isFiniteLocallyFreeOfRank_free (R := X.ringCatSheaf) r).isFiniteLocallyFree).hom ≫
      dualMap (pullbackFreeIso p r).inv = coordinateInverse Y r := by
  apply freeHom_ext_top
  intro i
  apply (freeDualCoordinates Y r).injective
  funext j
  change evalAt (freeOn Y r)
      ((dualMap (pullbackFreeIso p r).inv).app ⊤
        ((Stacks.FundamentalGroup.pullbackDualSheafIso p (freeOn X r)
          (SheafOfModules.isFiniteLocallyFreeOfRank_free (R := X.ringCatSheaf) r).isFiniteLocallyFree).hom.app ⊤
          (((Scheme.Modules.pullback p).map (coordinateInverse X r)).app ⊤
            ((pullbackFreeIso p r).inv.app ⊤ (freeBasisSection Y r i)))))
      (freeBasisSection Y r j) = _
  rw [evalAt_eq_dualPairing, dualPairing_dualMap]
  change evalAt ((Scheme.Modules.pullback p).obj (freeOn X r))
    ((Stacks.FundamentalGroup.pullbackDualSheafIso p (freeOn X r)
      (SheafOfModules.isFiniteLocallyFreeOfRank_free (R := X.ringCatSheaf) r).isFiniteLocallyFree).hom.app ⊤
      (((Scheme.Modules.pullback p).map (coordinateInverse X r)).app ⊤
        ((pullbackFreeIso p r).inv.app ⊤ (freeBasisSection Y r i))))
    ((pullbackFreeIso p r).inv.app ⊤ (freeBasisSection Y r j)) =
    evalAt (freeOn Y r) ((coordinateInverse Y r).app ⊤ (freeBasisSection Y r i))
      (freeBasisSection Y r j)
  rw [FiniteFreeBasisPullback.inverse_freeBasisSection_pullback,
    FiniteFreeBasisPullback.inverse_freeBasisSection_pullback,
    pullback_map_app_pullbackGlobalSections, evalAt_pullbackGlobalSections,
    coordinateInverse_eval, coordinateInverse_eval]
  split_ifs <;> simp

theorem coordinateInverse_eq_inv (X : Scheme.{u}) (r : ℕ) :
    coordinateInverse X r = (coordinatesIso X r).inv := by
  apply (cancel_mono (coordinatesMap X r)).1
  rw [coordinateInverse_comp_coordinatesMap]
  change 𝟙 _ = (coordinatesIso X r).inv ≫ (coordinatesIso X r).hom
  exact (coordinatesIso X r).inv_hom_id.symm

/-- The exact original dual-to-free coordinate map is compatible with
the canonical native pullback and canonical native dual base change. -/
theorem coordinatesMap_pullback (r : ℕ) :
    (Scheme.Modules.pullback p).map (coordinatesMap X r) ≫ (pullbackFreeIso p r).hom =
      (Stacks.FundamentalGroup.pullbackDualSheafIso p (freeOn X r)
        (SheafOfModules.isFiniteLocallyFreeOfRank_free (R := X.ringCatSheaf) r).isFiniteLocallyFree).hom ≫
        dualMap (pullbackFreeIso p r).inv ≫ coordinatesMap Y r := by
  let : IsIso (coordinateInverse X r) := by rw [coordinateInverse_eq_inv]; infer_instance
  apply (cancel_epi ((Scheme.Modules.pullback p).map (coordinateInverse X r))).1
  calc
    _ = (pullbackFreeIso p r).hom := by
      rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
        coordinateInverse_comp_coordinatesMap, CategoryTheory.Functor.map_id, Category.id_comp]
    _ = _ := by
      have h := congrArg (fun a => (pullbackFreeIso p r).hom ≫ a ≫ coordinatesMap Y r)
        (coordinateInverse_pullback p r)
      simpa only [Category.assoc, Iso.hom_inv_id_assoc,
        coordinateInverse_comp_coordinatesMap, Category.comp_id] using h.symm

def pulledQuotient {Q : X.Modules} {r : ℕ} (q : freeOn X r ⟶ Q) :
    freeOn Y r ⟶ (Scheme.Modules.pullback p).obj Q :=
  (pullbackFreeIso p r).inv ≫ (Scheme.Modules.pullback p).map q

/-- The actual pulled inverse-quotient line is exactly the actual dual
of the actual pulled quotient, in the same original free coordinates. -/
theorem pointLineMap_pullback {Q : X.Modules} {r : ℕ} (q : freeOn X r ⟶ Q)
    (hQ : SheafOfModules.IsFiniteLocallyFree.{u,u,u} Q) :
    (Scheme.Modules.pullback p).map (pointLineMap q) ≫ (pullbackFreeIso p r).hom =
      (Stacks.FundamentalGroup.pullbackDualSheafIso p Q hQ).hom ≫
        pointLineMap (pulledQuotient p q) := by
  let hF := (SheafOfModules.isFiniteLocallyFreeOfRank_free (R := X.ringCatSheaf) r).isFiniteLocallyFree
  have hn : (Scheme.Modules.pullback p).map (dualMap q) ≫
      (Stacks.FundamentalGroup.pullbackDualSheafIso p (freeOn X r) hF).hom =
      (Stacks.FundamentalGroup.pullbackDualSheafIso p Q hQ).hom ≫
        dualMap ((Scheme.Modules.pullback p).map q) :=
    Stacks.Chow.pullbackDualMap_naturality p q
  change (Scheme.Modules.pullback p).map (dualMap q ≫ coordinatesMap X r) ≫
    (pullbackFreeIso p r).hom = _
  rw [CategoryTheory.Functor.map_comp, Category.assoc, coordinatesMap_pullback]
  have hn' := congrArg (fun a => a ≫ dualMap (pullbackFreeIso p r).inv ≫ coordinatesMap Y r) hn
  simpa only [pointLineMap, pulledQuotient, dualMap_comp, Category.assoc] using hn'

section PointField

variable (K : Type u) [Field K] [CharZero K]

/-- Literal framed quotient coordinates construct an actual preimage
of the original point vector in the actual dual quotient line. -/
theorem pointSection_preimage {Q : (Spec (.of K)).Modules}
    (q : freeOn (Spec (.of K)) 14 ⟶ Q)
    (e : Q ≅ SheafOfModules.unit (Spec (.of K)).ringCatSheaf)
    (v : LagrangianField.Primitive K)
    (h : ∀ j : Fin 14, LinearIncidenceTensorCoordinates.unitCoordinate (Spec (.of K))
      (e.hom.app ⊤ (q.app ⊤ (freeBasisSection (Spec (.of K)) 14 j))) =
        (Scheme.ΓSpecIso (.of K)).inv.hom
          ((LagrangianPluckerLinear.primitiveBasis14 K).repr v j)) :
    ∃ a : Γ(dualSheaf Q, ⊤), (pointLineMap q).app ⊤ a =
      MukaiCubicFreeSheaf.pointSection K (𝟙 (Spec (.of K))) v := by
  refine ⟨LagrangianLocalIsotropy.functionalSection Q e.hom,?_⟩
  apply (freeSectionCoordinates (Spec (.of K)) 14).injective
  funext j
  rw [pointLineMap_coordinates, LagrangianLocalIsotropy.evalAt_functionalSection,
    MukaiCubicFreeSheaf.pointSection_coordinates, MukaiFreePullbackCoordinates.baseScalar_id]
  exact h j

end PointField

end M9Native.MukaiDualPullbackSections
