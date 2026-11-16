module
public import M9StacksIntegration.FreeTwoProjectiveChartCoordinates

@[expose] public noncomputable section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf
universe u
namespace M9Native.SplitTwoFrameCoordinates
open LagrangianMatrixChart FreeTwoCoordinates
variable {X T : Scheme.{u}} (g : T ⟶ X) (t : Γ(T,⊤))

def coordinateMap : (Scheme.Modules.pullback g).obj (Scheme.unitModule X) ⟶
    Scheme.unitModule T :=
  (Scheme.Modules.pullbackUnitIso g).hom ≫
    Scheme.Modules.unitHomEquivTop (Scheme.unitModule T) t

def quotientMap (i : Fin 2) : (Scheme.Modules.pullback g).obj (freeOn X 2) ⟶
    Scheme.unitModule T :=
  (FreeTwoProjectiveCharts.splitting X i).splitQuotientMap (coordinateMap g t)

theorem inclusion_quotientMap (i : Fin 2) :
    (Scheme.Modules.pullback g).map (FreeTwoCoordinates.inclusion X i) ≫ quotientMap g t i =
      (Scheme.Modules.pullbackUnitIso g).hom :=
  (FreeTwoProjectiveCharts.splitting X i).map_σ_comp_splitQuotientMap (coordinateMap g t)

theorem other_inclusion_quotientMap (i : Fin 2) :
    (Scheme.Modules.pullback g).map (FreeTwoCoordinates.inclusion X (other i)) ≫
      quotientMap g t i = coordinateMap g t :=
  (FreeTwoProjectiveCharts.splitting X i).map_σ'_comp_splitQuotientMap (coordinateMap g t)

theorem inclusion_pullback_one (j : Fin 2) :
    ((Scheme.Modules.pullback g).map (FreeTwoCoordinates.inclusion X j)).app ⊤
      (pullbackGlobalSections g (Scheme.unitModule X) (1 : Γ(X,⊤))) =
        pullbackGlobalSections g (freeOn X 2) (freeBasisSection X 2 j) :=
  SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections g (FreeTwoCoordinates.inclusion X j) _

theorem quotientMap_basis (i j : Fin 2) :
    (quotientMap g t i).app ⊤
      (pullbackGlobalSections g (freeOn X 2) (freeBasisSection X 2 j)) =
        if j=i then (1 : Γ(T,⊤)) else t := by
  by_cases hj : j=i
  · subst j
    rw [ite_eq_left rfl,← inclusion_pullback_one g]
    change Scheme.Modules.Hom.app
      ((Scheme.Modules.pullback g).map (FreeTwoCoordinates.inclusion X i) ≫ quotientMap g t i)
      ⊤ (pullbackGlobalSections g (Scheme.unitModule X) (1 : Γ(X,⊤))) = _
    rw [inclusion_quotientMap]
    exact (SectionsEqualizer.pullbackUnitIso_unit g (1 : Γ(X,⊤))).trans (map_one g.appTop.hom)
  · have hj' : j=other i := by fin_cases i <;> fin_cases j <;> simp_all [other]
    rw [ite_eq_right hj,hj',← inclusion_pullback_one g]
    change Scheme.Modules.Hom.app
      ((Scheme.Modules.pullback g).map (FreeTwoCoordinates.inclusion X (other i)) ≫
        quotientMap g t i) ⊤ (pullbackGlobalSections g (Scheme.unitModule X) (1 : Γ(X,⊤))) = _
    rw [other_inclusion_quotientMap]
    change (Scheme.Modules.unitHomEquivTop (Scheme.unitModule T) t).app ⊤
      ((Scheme.Modules.pullbackUnitIso g).hom.app ⊤
        (pullbackGlobalSections g (Scheme.unitModule X) (1 : Γ(X,⊤)))) = _
    have h1 : (Scheme.Modules.pullbackUnitIso g).hom.app ⊤
        (pullbackGlobalSections g (Scheme.unitModule X) (1 : Γ(X,⊤))) = (1 : Γ(T,⊤)) :=
      (SectionsEqualizer.pullbackUnitIso_unit g (1 : Γ(X,⊤))).trans (map_one g.appTop.hom)
    exact (congrArg ((Scheme.Modules.unitHomEquivTop (Scheme.unitModule T) t).app ⊤) h1).trans
      (Stacks.RelativeProj.UnitSplitting.unitHomEquivTop_app_top_of_eq_one _ _ _ rfl)

/-- The full coordinate formula uses the actual three maps and actual
frame. The map-level triangle is provided by the genuine native
classifier in the application, not a desired coordinate formula. -/
theorem frame_coordinate {P : Scheme.{u}} (p : P ⟶ X) (L : P.Modules)
    (q : (Scheme.Modules.pullback p).obj (freeOn X 2) ⟶ L)
    (f : T ⟶ P) (hg : f ≫ p = g) (i : Fin 2)
    (e : (Scheme.Modules.pullback f).obj L ≅ Scheme.unitModule T)
    (he : (Scheme.Modules.pullbackCongr hg).inv.app (freeOn X 2) ≫
      Stacks.Modules.quotientMapAlong p q f ≫ e.hom = quotientMap g t i)
    (j : Fin 2) :
    e.hom.app ⊤ (pullbackGlobalSections f L
      (q.app ⊤ (pullbackGlobalSections p (freeOn X 2) (freeBasisSection X 2 j)))) =
        if j=i then (1 : Γ(T,⊤)) else t := by
  have hquot := FreeTwoProjectiveChartCoordinates.quotientMapAlong_global p (freeOn X 2) L q
    f g hg (freeBasisSection X 2 j)
  have heval := (congrArg (e.hom.app ⊤) hquot).symm
  have hbasis := quotientMap_basis g t i j
  rw [← he] at hbasis
  exact heval.trans hbasis

end M9Native.SplitTwoFrameCoordinates
