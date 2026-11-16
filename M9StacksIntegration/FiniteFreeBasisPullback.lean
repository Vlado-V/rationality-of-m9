module

public import M9StacksIntegration.LagrangianGrassmannian
public import M9StacksIntegration.LagrangianMatrixChart

/-! The actual canonical free-sheaf pullback comparison preserves every native
finite basis section, and the pulled quotient map retains its actual basis values.
This is the frozen rank-six proof, with the finite rank made explicit. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace M9Native.FiniteFreeBasisPullback
open M9Native.LagrangianGrassmannian M9Native.LagrangianMatrixChart
open M9Native.LagrangianPullback M9Native.SectionZeroIdealFactorization
open AlgebraicGeometry.Grassmannian

theorem freeBasisSection_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) (r : ℕ) (i : Fin r) :
    (pullbackFreeIso f r).hom.app ⊤
      (pullbackGlobalSections f (freeOn X r) (freeBasisSection X r i))=freeBasisSection Y r i := by
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  have hnat := pullback_map_app_pullbackGlobalSections f
    (SheafOfModules.ιFree (R:=X.ringCatSheaf) (ULift.up.{u} i)) (1 : Γ(X,⊤))
  have hcomp := congrArg (fun φ => φ.val.app (op ⊤)
    (pullbackGlobalSections f (SheafOfModules.unit X.ringCatSheaf) (1 : Γ(X,⊤))))
      (pullback_map_ιFree_comp_pullbackFreeIso_hom f r (ULift.up.{u} i))
  change (pullbackFreeIso f r).hom.app ⊤
    (pullbackGlobalSections f (freeOn X r)
      ((SheafOfModules.ιFree (R:=X.ringCatSheaf) (ULift.up.{u} i)).val.app (op ⊤) (1 : Γ(X,⊤))))=_
  exact (congrArg ((pullbackFreeIso f r).hom.app ⊤) hnat.symm).trans
    (hcomp.trans (congrArg
      ((SheafOfModules.ιFree (R:=Y.ringCatSheaf) (ULift.up.{u} i)).val.app (op ⊤)) (unit_pullback_one f)))

theorem inverse_freeBasisSection_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) (r : ℕ) (i : Fin r) :
    (pullbackFreeIso f r).inv.app ⊤ (freeBasisSection Y r i)=
      pullbackGlobalSections f (freeOn X r) (freeBasisSection X r i) := by
  have h := congrArg ((pullbackFreeIso f r).inv.app ⊤) (freeBasisSection_pullback f r i)
  have he := congrArg (fun φ => φ.app ⊤
    (pullbackGlobalSections f (freeOn X r) (freeBasisSection X r i))) (pullbackFreeIso f r).hom_inv_id
  exact h.symm.trans he

theorem pullbackPresentation_basis {X Y : Scheme.{u}} (f : Y ⟶ X) {k n : ℕ}
    (q : QuotientPresentation X k n) (i : Fin n) :
    Scheme.Modules.Hom.app (X:=Y) (pullbackPresentation f q).map ⊤ (freeBasisSection Y n i)=
      pullbackGlobalSections f q.target (Scheme.Modules.Hom.app (X:=X) q.map ⊤ (freeBasisSection X n i)) := by
  change ((Scheme.Modules.pullback f).map q.map).app ⊤
    ((pullbackFreeIso f n).inv.app ⊤ (freeBasisSection Y n i))=_
  rw [inverse_freeBasisSection_pullback]
  exact pullback_map_app_pullbackGlobalSections f q.map _

end M9Native.FiniteFreeBasisPullback
end
