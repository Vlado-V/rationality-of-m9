module

public import M9StacksIntegration.LinearIncidenceTensorCoordinates
public import M9StacksIntegration.LagrangianGrassmannian

/-! Actual line-frame coordinates commute with pullback. This pins the local
incidence coefficients as genuine base-ring coefficients on affine-space charts. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf
namespace M9Native.LineFramePullback
open M9Native.LinearIncidenceTensorCoordinates M9Native.LagrangianGrassmannian
open M9Native.SectionZeroIdealFactorization

def unitIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ≅
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) := by
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  let : (TopologicalSpace.Opens.map f.base).Final := final_of_representablyFlat _
  have h : IsIso (SheafOfModules.pullbackObjUnitToUnit (F:=TopologicalSpace.Opens.map f.base)
      f.toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal f.toRingCatSheafHom
  exact @asIso _ _ _ _ _ h

/-- The actual canonical unit comparison sends a pulled function to its actual ring pullback. -/
theorem unitIso_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (r : Γ(Y,⊤)) :
    unitCoordinate X ((unitIso f).hom.app ⊤
      (pullbackGlobalSections f (SheafOfModules.unit Y.ringCatSheaf) r))=f.appTop r := by
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  have heq : (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      (SheafOfModules.unit Y.ringCatSheaf) ≫ (Scheme.Modules.pushforward f).map
        (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)=
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    (Adjunction.homEquiv_unit _ _ _ _).symm.trans
      (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _)
  change (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom).val.app (op ⊤)
    (pullbackGlobalSections f (SheafOfModules.unit Y.ringCatSheaf) r)=f.appTop r
  rw [pullbackGlobalSections_eq_unit]
  exact congrArg (fun φ => φ.val.app (op ⊤) r) heq

/-- Pulling an actual frame and applying the native unit comparison gives an actual frame. -/
def pullbackFrame {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    (e : L ≅ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)) :
    (Scheme.Modules.pullback f).obj L ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  (Scheme.Modules.pullback f).mapIso e ≪≫ unitIso f

theorem pullbackFrame_coordinate {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    (e : L ≅ (SheafOfModules.unit Y.ringCatSheaf : Y.Modules)) (s : Γ(L,⊤)) :
    unitCoordinate X ((pullbackFrame f L e).hom.app ⊤ (pullbackGlobalSections f L s))=
      f.appTop (unitCoordinate Y (e.hom.app ⊤ s)) := by
  exact (congrArg (fun t => unitCoordinate X ((unitIso f).hom.app ⊤ t))
    (pullback_map_app_pullbackGlobalSections f e.hom s)).trans (unitIso_apply f _)

theorem pullbackComp_inv_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (L : Z.Modules) (s : Γ(L,⊤)) :
    ((Scheme.Modules.pullbackComp f g).inv.app L).app ⊤
      (pullbackGlobalSections (f ≫ g) L s)=
        pullbackGlobalSections f ((Scheme.Modules.pullback g).obj L)
          (pullbackGlobalSections g L s) := by
  have h := congrArg (((Scheme.Modules.pullbackComp f g).inv.app L).app ⊤)
    (AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp f g L s)
  have he := congrArg (fun φ => φ.app ⊤
      (pullbackGlobalSections f ((Scheme.Modules.pullback g).obj L)
        (pullbackGlobalSections g L s))) ((Scheme.Modules.pullbackComp f g).app L).hom_inv_id
  exact h.symm.trans he

/-- The actual comparison of iterated pullbacks around a commutative square. -/
def squareIso {P Y X Z : Scheme.{u}} (q : P ⟶ Y) (a : Y ⟶ Z)
    (p : P ⟶ X) (f : X ⟶ Z) (h : q ≫ a=p ≫ f) (L : Z.Modules) :
    (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback a).obj L) ≅
      (Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback f).obj L) :=
  (Scheme.Modules.pullbackComp q a).app L ≪≫
    (Scheme.Modules.pullbackCongr h).app L ≪≫
      ((Scheme.Modules.pullbackComp p f).app L).symm

theorem squareIso_apply {P Y X Z : Scheme.{u}} (q : P ⟶ Y) (a : Y ⟶ Z)
    (p : P ⟶ X) (f : X ⟶ Z) (h : q ≫ a=p ≫ f) (L : Z.Modules) (s : Γ(L,⊤)) :
    (squareIso q a p f h L).hom.app ⊤
      (pullbackGlobalSections q ((Scheme.Modules.pullback a).obj L)
        (pullbackGlobalSections a L s))=
      pullbackGlobalSections p ((Scheme.Modules.pullback f).obj L)
        (pullbackGlobalSections f L s) := by
  have hc := AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp q a L s
  have hn := AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_congr h L s
  exact (congrArg (fun t => ((Scheme.Modules.pullbackComp p f).inv.app L).app ⊤
    (((Scheme.Modules.pullbackCongr h).hom.app L).app ⊤ t)) hc).trans
      ((congrArg (((Scheme.Modules.pullbackComp p f).inv.app L).app ⊤) hn).trans
        (pullbackComp_inv_apply p f L s))

def squareFrame {P Y X Z : Scheme.{u}} (q : P ⟶ Y) (a : Y ⟶ Z)
    (p : P ⟶ X) (f : X ⟶ Z) (h : q ≫ a=p ≫ f) (L : Z.Modules)
    (e : (Scheme.Modules.pullback f).obj L ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :
    (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback a).obj L) ≅
      (SheafOfModules.unit P.ringCatSheaf : P.Modules) :=
  squareIso q a p f h L ≪≫ pullbackFrame p ((Scheme.Modules.pullback f).obj L) e

theorem squareFrame_coordinate {P Y X Z : Scheme.{u}} (q : P ⟶ Y) (a : Y ⟶ Z)
    (p : P ⟶ X) (f : X ⟶ Z) (h : q ≫ a=p ≫ f) (L : Z.Modules)
    (e : (Scheme.Modules.pullback f).obj L ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (s : Γ(L,⊤)) :
    unitCoordinate P ((squareFrame q a p f h L e).hom.app ⊤
      (pullbackGlobalSections q ((Scheme.Modules.pullback a).obj L)
        (pullbackGlobalSections a L s)))=
      p.appTop (unitCoordinate X (e.hom.app ⊤ (pullbackGlobalSections f L s))) := by
  exact (congrArg (fun t => unitCoordinate P
    ((pullbackFrame p ((Scheme.Modules.pullback f).obj L) e).hom.app ⊤ t))
      (squareIso_apply q a p f h L s)).trans (pullbackFrame_coordinate p _ e _)

end M9Native.LineFramePullback
end
