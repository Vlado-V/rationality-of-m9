module

public import M9StacksIntegration.PullbackCompositeVectorFrame
public import M9StacksIntegration.QuotientSectionMorphism

/-! Actual sections of two compatible quotient maps in a commuting
scheme square. All four maps and both quotients remain parameters. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.presheaf
namespace M9Native.PullbackQuotientSquare

variable {X Y P Q : Scheme.{u}} (g : Y ⟶ X) (p : P ⟶ X) (q : Q ⟶ Y) (b : Q ⟶ P)
  (hh : b ≫ p = q ≫ g) (E : X.Modules)

def sourceIso :
    (Scheme.Modules.pullback q).obj ((Scheme.Modules.pullback g).obj E) ≅
      (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback p).obj E) :=
  (Scheme.Modules.pullbackComp q g).app E ≪≫
    (Scheme.Modules.pullbackCongr hh.symm).app E ≪≫
    ((Scheme.Modules.pullbackComp b p).app E).symm

theorem sourceIso_apply (s : Γ(E,⊤)) :
    (sourceIso g p q b hh E).hom.app ⊤
      (pullbackGlobalSections q ((Scheme.Modules.pullback g).obj E)
        (pullbackGlobalSections g E s)) =
      pullbackGlobalSections b ((Scheme.Modules.pullback p).obj E)
        (pullbackGlobalSections p E s) := by
  change ((Scheme.Modules.pullbackComp b p).inv.app E).app ⊤
    (((Scheme.Modules.pullbackCongr hh.symm).hom.app E).app ⊤
      (((Scheme.Modules.pullbackComp q g).hom.app E).app ⊤
        (pullbackGlobalSections q ((Scheme.Modules.pullback g).obj E)
          (pullbackGlobalSections g E s)))) = _
  rw [SectionsEqualizer.pullbackGlobalSections_comp,
    SectionsEqualizer.pullbackGlobalSections_congr,LineFramePullback.pullbackComp_inv_apply]

theorem sourceIso_inv_apply (s : Γ(E,⊤)) :
    (sourceIso g p q b hh E).inv.app ⊤
      (pullbackGlobalSections b ((Scheme.Modules.pullback p).obj E)
        (pullbackGlobalSections p E s)) =
      pullbackGlobalSections q ((Scheme.Modules.pullback g).obj E)
        (pullbackGlobalSections g E s) := by
  have h := congrArg ((sourceIso g p q b hh E).inv.app ⊤)
    (sourceIso_apply g p q b hh E s)
  have he := congrArg (fun z => z.app ⊤
    (pullbackGlobalSections q ((Scheme.Modules.pullback g).obj E)
      (pullbackGlobalSections g E s))) (sourceIso g p q b hh E).hom_inv_id
  exact h.symm.trans he

variable (E' : Y.Modules) (u : (Scheme.Modules.pullback g).obj E ⟶ E')
  (L : P.Modules) (L' : Q.Modules)
  (v : (Scheme.Modules.pullback p).obj E ⟶ L)
  (v' : (Scheme.Modules.pullback q).obj E' ⟶ L')
  (e : (Scheme.Modules.pullback b).obj L ≅ L')
  (hv : (sourceIso g p q b hh E).hom ≫ (Scheme.Modules.pullback b).map v ≫ e.hom =
    (Scheme.Modules.pullback q).map u ≫ v')

include hv in
theorem quotient_section (s : Γ(E,⊤)) :
    e.hom.app ⊤ (pullbackGlobalSections b L
      (v.app ⊤ (pullbackGlobalSections p E s))) =
      v'.app ⊤ (pullbackGlobalSections q E'
        (u.app ⊤ (pullbackGlobalSections g E s))) := by
  have h := congrArg (fun z => z.app ⊤
    (pullbackGlobalSections q ((Scheme.Modules.pullback g).obj E)
      (pullbackGlobalSections g E s))) hv
  change e.hom.app ⊤ (((Scheme.Modules.pullback b).map v).app ⊤
    ((sourceIso g p q b hh E).hom.app ⊤
      (pullbackGlobalSections q ((Scheme.Modules.pullback g).obj E)
        (pullbackGlobalSections g E s)))) =
    v'.app ⊤ (((Scheme.Modules.pullback q).map u).app ⊤
      (pullbackGlobalSections q ((Scheme.Modules.pullback g).obj E)
        (pullbackGlobalSections g E s))) at h
  rw [sourceIso_apply,SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections,
    SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections] at h
  exact h

end M9Native.PullbackQuotientSquare
