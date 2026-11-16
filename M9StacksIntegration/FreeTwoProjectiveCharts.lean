module

public import M9StacksIntegration.FreeTwoCoordinates
public import M9StacksIntegration.LineFramePullback
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.SplitQuotientComplementAffineSpace
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.OverQuotients
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.FlagBundleUnconditional

/-!
# Actual affine-line charts of the original projective bundle of free two-space

The native unconditional invertible-quotient universal property constructs
the chart and its actual tautological quotient frame.  The actual comparison
of the two projective-bundle presentations retains the original Chow.bundle.
No projective or line-bundle comparison is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Chow Stacks.RelativeProj Stacks.Divisors

universe u
namespace M9Native.FreeTwoProjectiveCharts
open FreeTwoCoordinates LagrangianMatrixChart

variable (X : Scheme.{u})

instance freeTwo_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (freeOn X 2) 2 :=
  AlgebraicGeometry.Grassmannian.free_isFiniteLocallyFreeOfRank X 2

instance freeTwo_finite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (freeOn X 2) :=
  (freeTwo_rank X).isFiniteLocallyFree

instance freeTwo_quasicoherent : (freeOn X 2).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree _

instance unit_quasicoherent : (Scheme.unitModule X).IsQuasicoherent := by infer_instance

instance coordinateProjection_splitEpi (i : Fin 2) :
    IsSplitEpi (FreeTwoCoordinates.projection X i) :=
  ⟨⟨FreeTwoCoordinates.inclusion X i, inclusion_projection_self X i⟩⟩

/-- The genuine decomposition with coordinate i as the unit summand. -/
def splitting (i : Fin 2) :
    UnitSplitting (FreeTwoCoordinates.projection X (other i)) where
  σ := FreeTwoCoordinates.inclusion X i
  τ := FreeTwoCoordinates.projection X i
  σ' := FreeTwoCoordinates.inclusion X (other i)
  hsplit := splitting_identity X i
  hσu := inclusion_projection_other X i
  hστ := inclusion_projection_self X i
  hσ'τ := by rw [inclusion_projection,ite_eq_right (other_ne_self i)]
  hσ'u := inclusion_projection_self X (other i)

abbrev CoordinateIndex := ULift.{u} (Fin 1)
abbrev chartSpace : Scheme.{u} := 𝔸(CoordinateIndex.{u}; X)
abbrev toBase : chartSpace X ⟶ X := chartSpace X ↘ X
abbrev projectiveBundleSpace : Scheme.{u} := bundle (freeOn X 2)
abbrev projectiveBundleProjection : projectiveBundleSpace X ⟶ X := bundleProj (freeOn X 2)
abbrev tautologicalLine : (projectiveBundleSpace X).Modules := bundleTwist (freeOn X 2)

/-- The genuine native split-quotient chart, before the actual presentation comparison. -/
def nativeChart (i : Fin 2) : chartSpace X ⟶ projectiveBundle X (freeOn X 2) :=
  (splitting X i).affineSpaceToProjectiveBundle (singleBasis X)

@[reassoc] theorem nativeChart_projection (i : Fin 2) :
    nativeChart X i ≫ projectiveBundleToBase X (freeOn X 2) = toBase X :=
  (splitting X i).affineSpaceToProjectiveBundle_comp (singleBasis X)

instance nativeChart_isOpenImmersion (i : Fin 2) : IsOpenImmersion (nativeChart X i) := by
  change IsOpenImmersion ((splitting X i).affineSpaceToProjectiveBundle (singleBasis X))
  rw [← (splitting X i).splitQuotientComplementIso_inv_ι (singleBasis X)]
  infer_instance

/-- The actual chart in the SAME original projective bundle used by Chow and incidence. -/
def chart (i : Fin 2) : chartSpace X ⟶ projectiveBundleSpace X :=
  nativeChart X i ≫ (bundlePresentationIso (freeOn X 2)).inv

instance chart_isOpenImmersion (i : Fin 2) : IsOpenImmersion (chart X i) := by
  dsimp [chart]
  infer_instance

@[reassoc] theorem chart_projection (i : Fin 2) :
    chart X i ≫ projectiveBundleProjection X = toBase X := by
  change (nativeChart X i ≫ (bundlePresentationIso (freeOn X 2)).inv) ≫
    (symGradedBundle (freeOn X 2)).toBase = _
  rw [Category.assoc,bundlePresentationIso_inv_comp_toBase]
  exact nativeChart_projection X i

def coordinate : Γ(chartSpace X, ⊤) := AffineSpace.coord X (ULift.up.{u} (0 : Fin 1))

def coordinateMap :
    (Scheme.Modules.pullback (toBase X)).obj (Scheme.unitModule X) ⟶
      Scheme.unitModule (chartSpace X) :=
  UnitSplitting.ofCoordVector (singleBasis X) (toBase X) (AffineSpace.coord X)

def chartQuotientMap (i : Fin 2) :
    (Scheme.Modules.pullback (toBase X)).obj (freeOn X 2) ⟶
      Scheme.unitModule (chartSpace X) :=
  (splitting X i).splitQuotientMap (coordinateMap X)

def chartQuotient (i : Fin 2) :
    InvertibleQuotient (chartSpace X) ((Scheme.Modules.pullback (toBase X)).obj (freeOn X 2)) :=
  (splitting X i).splitQuotient (coordinateMap X)

/-- The actual original tautological quotient pulled to the actual chart. -/
def pulledTautological (i : Fin 2) :
    (Scheme.Modules.pullback (toBase X)).obj (freeOn X 2) ⟶
      (Scheme.Modules.pullback (chart X i)).obj (tautologicalLine X) :=
  (Scheme.Modules.pullbackCongr (chart_projection X i)).inv.app (freeOn X 2) ≫
    Stacks.Modules.quotientMapAlong (projectiveBundleProjection X)
      (bundleTautological (freeOn X 2)) (chart X i)

/-- The actual invertible-quotient classification supplies a frame of the
original O(1), with its original tautological map retained. -/
theorem exists_chartFrame (i : Fin 2) :
    ∃ e : (Scheme.Modules.pullback (chart X i)).obj (tautologicalLine X) ≅
        Scheme.unitModule (chartSpace X),
      pulledTautological X i ≫ e.hom = chartQuotientMap X i := by
  let F := freeOn X 2
  let F' := (Scheme.Modules.pullback (toBase X)).obj F
  obtain ⟨α,hα⟩ := (splitting X i).exists_overQuotientMap_splitClassifyingMorphism_comp
    (toBase X) (coordinateMap X)
  have hn : projectiveBundleOverEquiv F' (Iso.refl _)
      ⟨nativeChart X i,nativeChart_projection X i⟩ =
        Quotient.mk (invertibleQuotientSetoid (chartSpace X) F') (chartQuotient X i) := by
    apply (projectiveBundleOverEquiv_eq_iff F' (Iso.refl _) _ _).mpr
    refine ⟨α,?_⟩
    change 𝟙 ((Scheme.Modules.pullback (toBase X)).obj (freeOn X 2)) ≫
      (tautologicalDatum (freeOn X 2)).overQuotientMap
        ((splitting X i).splitClassifyingMorphism (toBase X) (coordinateMap X))
        ((splitting X i).splitClassifyingMorphism_comp (toBase X) (coordinateMap X)) ≫ α.hom =
          (splitting X i).splitQuotientMap (coordinateMap X)
    rw [Category.id_comp]
    exact hα
  have hs : symGradedOverEquiv F' (Iso.refl _)
      ⟨chart X i,chart_projection X i⟩ =
        Quotient.mk (invertibleQuotientSetoid (chartSpace X) F') (chartQuotient X i) := by
    change projectiveBundleOverEquiv F' (Iso.refl _)
      (symGradedOverMorphismEquiv ⟨chart X i,chart_projection X i⟩) = _
    have hh : symGradedOverMorphismEquiv ⟨chart X i,chart_projection X i⟩ =
        ⟨nativeChart X i,nativeChart_projection X i⟩ := by
      apply Subtype.ext
      change (nativeChart X i ≫ (bundlePresentationIso F).inv) ≫
        (bundlePresentationIso F).hom = nativeChart X i
      rw [Category.assoc,Iso.inv_hom_id,Category.comp_id]
    rw [hh]
    exact hn
  obtain ⟨e,he⟩ := (symGradedOverEquiv_eq_iff F' (Iso.refl _)
    ⟨chart X i,chart_projection X i⟩ (chartQuotient X i)).mp hs
  refine ⟨e,?_⟩
  change 𝟙 ((Scheme.Modules.pullback (toBase X)).obj (freeOn X 2)) ≫
    (Scheme.Modules.pullbackCongr (chart_projection X i)).inv.app (freeOn X 2) ≫
      Stacks.Modules.quotientMapAlong (projectiveBundleProjection X)
        (bundleTautological (freeOn X 2)) (chart X i) ≫ e.hom = chartQuotientMap X i at he
  rw [Category.id_comp] at he
  exact (Category.assoc _ _ _).trans he

/-- The actual original tautological-line frame produced by that proof. -/
def chartFrame (i : Fin 2) :
    (Scheme.Modules.pullback (chart X i)).obj (tautologicalLine X) ≅
      Scheme.unitModule (chartSpace X) :=
  Classical.choose (exists_chartFrame X i)

theorem chartFrame_triangle (i : Fin 2) :
    pulledTautological X i ≫ (chartFrame X i).hom = chartQuotientMap X i :=
  Classical.choose_spec (exists_chartFrame X i)

/-- The two original tautological coordinate sections used by the incidence tensor. -/
def tautCoordinate (j : Fin 2) : Γ(tautologicalLine X, ⊤) :=
  (bundleTautological (freeOn X 2)).app ⊤
    (pullbackGlobalSections (projectiveBundleProjection X) (freeOn X 2) (freeBasisSection X 2 j))

end M9Native.FreeTwoProjectiveCharts
