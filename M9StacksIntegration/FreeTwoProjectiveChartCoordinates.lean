module

public import M9StacksIntegration.FreeTwoProjectiveCharts

/-! # Literal (1,t) and (t,1) coordinates of the original tautological quotient -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Chow Stacks.RelativeProj
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf
namespace M9Native.FreeTwoProjectiveChartCoordinates

open FreeTwoCoordinates FreeTwoProjectiveCharts LagrangianMatrixChart
open SectionZeroIdealFactorization

/-- The actual quotient along an actual composite retains actual pulled global sections. -/
theorem quotientMapAlong_global {X P T : Scheme.{u}} (p : P ⟶ X)
    (F : X.Modules) (L : P.Modules) (q : (Scheme.Modules.pullback p).obj F ⟶ L)
    (f : T ⟶ P) (g : T ⟶ X) (hg : f ≫ p = g) (s : Γ(F,⊤)) :
    Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackCongr hg).inv.app F ≫ Stacks.Modules.quotientMapAlong p q f)
      ⊤ (pullbackGlobalSections g F s) =
        pullbackGlobalSections f L (q.app ⊤ (pullbackGlobalSections p F s)) := by
  subst g
  change (Stacks.Modules.quotientMapAlong p q f).app ⊤
    (pullbackGlobalSections (f ≫ p) F s) = _
  change ((Scheme.Modules.pullback f).map q).app ⊤
    (((Scheme.Modules.pullbackComp f p).inv.app F).app ⊤
      (pullbackGlobalSections (f ≫ p) F s)) = _
  rw [LineFramePullback.pullbackComp_inv_apply,pullback_map_app_pullbackGlobalSections]

/-- The inverse canonical unit comparison sends one to its actual pullback. -/
theorem inverse_pullbackUnitIso_one {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullbackUnitIso f).inv.app ⊤ (1 : Γ(Y,⊤)) =
      pullbackGlobalSections f (Scheme.unitModule X) (1 : Γ(X,⊤)) := by
  have h := congrArg ((Scheme.Modules.pullbackUnitIso f).inv.app ⊤)
    ((SectionsEqualizer.pullbackUnitIso_unit f (1 : Γ(X,⊤))).trans (map_one f.appTop.hom))
  have he := congrArg (fun q => Scheme.Modules.Hom.app q ⊤
    (pullbackGlobalSections f (Scheme.unitModule X) (1 : Γ(X,⊤))))
    (Scheme.Modules.pullbackUnitIso f).hom_inv_id
  exact h.symm.trans he

variable (X : Scheme.{u})

theorem coordinateMap_eq : coordinateMap X =
    (Scheme.Modules.pullbackUnitIso (toBase X)).hom ≫
      Scheme.Modules.unitHomEquivTop (Scheme.unitModule (chartSpace X)) (coordinate X) := by
  have h : (Scheme.Modules.pullback (toBase X)).map
      (UnitSplitting.basisMap (singleBasis X) (ULift.up.{u} (0 : Fin 1))) ≫ coordinateMap X =
      (Scheme.Modules.pullbackUnitIso (toBase X)).hom ≫
        Scheme.Modules.unitHomEquivTop (Scheme.unitModule (chartSpace X)) (coordinate X) :=
    Cofan.IsColimit.fac (UnitSplitting.isColimitPullbackBasis (singleBasis X) (toBase X))
      (fun j => (Scheme.Modules.pullbackUnitIso (toBase X)).hom ≫
        Scheme.Modules.unitHomEquivTop (Scheme.unitModule (chartSpace X)) (AffineSpace.coord X j))
      (ULift.up.{u} (0 : Fin 1))
  rw [UnitSplitting.basisMap,inclusion_singleBasis] at h
  change (Scheme.Modules.pullback (toBase X)).map (𝟙 (Scheme.unitModule X)) ≫ coordinateMap X =
    (Scheme.Modules.pullbackUnitIso (toBase X)).hom ≫
      Scheme.Modules.unitHomEquivTop (Scheme.unitModule (chartSpace X)) (coordinate X) at h
  rw [CategoryTheory.Functor.map_id,Category.id_comp] at h
  exact h

/-- The pulled actual basis inclusion carries the pulled unit section to
its original actual pulled basis section. -/
theorem map_inclusion_pullback_one (j : Fin 2) :
    ((Scheme.Modules.pullback (toBase X)).map (FreeTwoCoordinates.inclusion X j)).app ⊤
      (pullbackGlobalSections (toBase X) (Scheme.unitModule X) (1 : Γ(X,⊤))) =
        pullbackGlobalSections (toBase X) (freeOn X 2) (freeBasisSection X 2 j) :=
  pullback_map_app_pullbackGlobalSections (toBase X) (FreeTwoCoordinates.inclusion X j) _

@[reassoc] theorem map_inclusion_chartQuotientMap (i : Fin 2) :
    (Scheme.Modules.pullback (toBase X)).map (FreeTwoCoordinates.inclusion X i) ≫
      chartQuotientMap X i = (Scheme.Modules.pullbackUnitIso (toBase X)).hom :=
  (splitting X i).map_σ_comp_splitQuotientMap (coordinateMap X)

@[reassoc] theorem map_other_inclusion_chartQuotientMap (i : Fin 2) :
    (Scheme.Modules.pullback (toBase X)).map (FreeTwoCoordinates.inclusion X (other i)) ≫
      chartQuotientMap X i = coordinateMap X :=
  (splitting X i).map_σ'_comp_splitQuotientMap (coordinateMap X)

/-- The actual rank-two quotient has the literal normalized coordinate pair. -/
theorem chartQuotientMap_basis (i j : Fin 2) :
    (chartQuotientMap X i).app ⊤
      (pullbackGlobalSections (toBase X) (freeOn X 2) (freeBasisSection X 2 j)) =
        if j=i then (1 : Γ(chartSpace X,⊤)) else coordinate X := by
  by_cases hj : j=i
  · subst j
    rw [ite_eq_left rfl,← map_inclusion_pullback_one]
    change Scheme.Modules.Hom.app
      ((Scheme.Modules.pullback (toBase X)).map (FreeTwoCoordinates.inclusion X i) ≫
        chartQuotientMap X i) ⊤
      (pullbackGlobalSections (toBase X) (Scheme.unitModule X) (1 : Γ(X,⊤))) = _
    rw [map_inclusion_chartQuotientMap]
    exact (SectionsEqualizer.pullbackUnitIso_unit (toBase X) (1 : Γ(X,⊤))).trans (map_one (toBase X).appTop.hom)
  · have hj' : j=other i := by fin_cases i <;> fin_cases j <;> simp_all [other]
    rw [ite_eq_right hj,hj',← map_inclusion_pullback_one]
    change Scheme.Modules.Hom.app
      ((Scheme.Modules.pullback (toBase X)).map (FreeTwoCoordinates.inclusion X (other i)) ≫
        chartQuotientMap X i) ⊤
      (pullbackGlobalSections (toBase X) (Scheme.unitModule X) (1 : Γ(X,⊤))) = _
    rw [map_other_inclusion_chartQuotientMap,coordinateMap_eq]
    change (Scheme.Modules.unitHomEquivTop (Scheme.unitModule (chartSpace X)) (coordinate X)).app ⊤
      ((Scheme.Modules.pullbackUnitIso (toBase X)).hom.app ⊤
        (pullbackGlobalSections (toBase X) (Scheme.unitModule X) (1 : Γ(X,⊤)))) = _
    have h1 : (Scheme.Modules.pullbackUnitIso (toBase X)).hom.app ⊤
        (pullbackGlobalSections (toBase X) (Scheme.unitModule X) (1 : Γ(X,⊤))) =
          (1 : Γ(chartSpace X,⊤)) :=
      (SectionsEqualizer.pullbackUnitIso_unit (toBase X) (1 : Γ(X,⊤))).trans
        (map_one (toBase X).appTop.hom)
    exact (congrArg
      ((Scheme.Modules.unitHomEquivTop (Scheme.unitModule (chartSpace X)) (coordinate X)).app ⊤)
      h1).trans (UnitSplitting.unitHomEquivTop_app_top_of_eq_one _ _ _ rfl)

/-- The actual original tautological coordinate is retained under the actual
canonical comparison of the original structural morphisms. -/
theorem pulledTautological_basis (i j : Fin 2) :
    (pulledTautological X i).app ⊤
      (pullbackGlobalSections (toBase X) (freeOn X 2) (freeBasisSection X 2 j)) =
        pullbackGlobalSections (chart X i) (tautologicalLine X) (tautCoordinate X j) :=
  quotientMapAlong_global (projectiveBundleProjection X) (freeOn X 2) (tautologicalLine X)
    (bundleTautological (freeOn X 2)) (chart X i) (toBase X) (chart_projection X i) _

/-- In the actual original O(1) frame, the actual original two coordinates
are exactly (1,t) on the first chart and (t,1) on the second chart. -/
theorem chartFrame_coordinate (i j : Fin 2) :
    (chartFrame X i).hom.app ⊤
      (pullbackGlobalSections (chart X i) (tautologicalLine X) (tautCoordinate X j)) =
        if j=i then (1 : Γ(chartSpace X,⊤)) else coordinate X := by
  calc
    _ = Scheme.Modules.Hom.app (pulledTautological X i ≫ (chartFrame X i).hom) ⊤
        (pullbackGlobalSections (toBase X) (freeOn X 2) (freeBasisSection X 2 j)) :=
      (congrArg ((chartFrame X i).hom.app ⊤) (pulledTautological_basis X i j)).symm
    _ = (chartQuotientMap X i).app ⊤
        (pullbackGlobalSections (toBase X) (freeOn X 2) (freeBasisSection X 2 j)) := by
      rw [chartFrame_triangle]
    _ = _ := chartQuotientMap_basis X i j

end M9Native.FreeTwoProjectiveChartCoordinates
