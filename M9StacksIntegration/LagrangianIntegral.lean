module

public import M9StacksIntegration.LagrangianAdmissibleCharts
public import StacksFrontier.Topology.Dimension.OpenCover
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Field
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Integrality of the actual Lagrangian Grassmannian

The eight genuine affine-six open charts have a common actual point: the quotient
with matrix `[I | I]`. Their irreducibility therefore gives irreducibility of the
actual zero-ideal scheme; reducedness descends from the same open cover.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix TopologicalSpace
open scoped BigOperators

universe u

namespace M9Native.LagrangianIntegral

open M9Native.LagrangianAdmissibleMinors M9Native.LagrangianAdmissibleCharts
open M9Native.LagrangianGrassmannian M9Native.LagrangianMatrixChart
open M9Native.LagrangianTransitivity M9Native.LagrangianSigmaInvariance
open AlgebraicGeometry.Grassmannian

variable (R : Type u) [CommRing R]

/-- The actual common quotient matrix, with both three-column blocks equal to the identity. -/
def graphMatrix : Matrix (Fin 3) (Fin 6) R := fun i j => if i.val=j.val%3 then 1 else 0

@[simp] theorem graphMatrix_first (i j : Fin 3) :
    graphMatrix R i (j.castAdd 3)=(if i=j then 1 else 0) := by
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem graphMatrix_last (i j : Fin 3) :
    graphMatrix R i (Fin.natAdd 3 j)=(if i=j then 1 else 0) := by
  fin_cases i <;> fin_cases j <;> rfl

theorem graphMatrix_admissible (s : Choice) :
    (graphMatrix R).submatrix id (embedding s)=1 := by
  ext i j
  change graphMatrix R i (column s j)=(if i=j then 1 else 0)
  by_cases hs : s j
  · simpa only [column,ite_eq_left hs] using graphMatrix_last R i j
  · simpa only [column,ite_eq_right hs] using graphMatrix_first R i j

@[simp] theorem graphMatrix_admissibleMinor (s : Choice) :
    admissibleMinor (graphMatrix R) s=1 := by
  rw [admissibleMinor,graphMatrix_admissible,Matrix.det_one]

@[simp] theorem graphMatrix_quotientSigma :
    M9Native.LagrangianRing.quotientSigma R (graphMatrix R)=0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply (exteriorPower.ιMulti R 2).map_eq_zero_of_eq _ (i:=0) (j:=1)
  · funext j
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
      graphMatrix_first,graphMatrix_last]
  · decide

/-- The normalized native chart point with its actual matrix equal to `[I | I]`. -/
def graphChartPoint (T : Scheme.{u}) : T ⟶
    Spec (.of (MvPolynomial (ChartIndex.{u} firstPivot) (ULift.{u} ℤ))) :=
  (AffineSpace.toSpecMvPolyIntEquiv _).symm
    (fun a => graphMatrix Γ(T,⊤) a.down.2 a.down.1.val)

def graphPresentation (T : Scheme.{u}) : QuotientPresentation T 3 6 :=
  LagrangianGrassmannian.chartPresentation firstPivot (graphChartPoint T)

theorem graphPresentation_matrix (T : Scheme.{u}) :
    Stacks.FreeSheafMatrix.toMatrix (graphPresentation T).map=graphMatrix Γ(T,⊤) := by
  change Stacks.FreeSheafMatrix.toMatrix
    (LagrangianGrassmannian.chartPresentation firstPivot (graphChartPoint T)).map=_
  rw [LagrangianGrassmannian.chartPresentation_map,toMatrix_chartQuotientMap]
  ext i j
  by_cases hj : j ∈ Set.range firstPivot
  · obtain ⟨j,rfl⟩ := hj
    rw [chartMatrix_apply_self]
    exact (graphMatrix_first _ i j).symm
  · rw [chartMatrix_apply_of_notMem firstPivot _ i hj]
    change (AffineSpace.toSpecMvPolyIntEquiv _
      ((AffineSpace.toSpecMvPolyIntEquiv _).symm _)) _=_
    rw [Equiv.apply_symm_apply]

theorem graphPresentation_annihilatesSigma (T : Scheme.{u}) :
    AnnihilatesSigma T (graphPresentation T).map := by
  have h := exteriorPowerMap_sigma_eq T (r:=3) (graphPresentation T).map
  rw [graphPresentation_matrix,← quotientSigma_eq_map,graphMatrix_quotientSigma,map_zero] at h
  exact h

section Geometry

variable (K : Type u) [Field K]

/-- The actual graph quotient determines a point factoring through every admissible chart. -/
theorem exists_common_chart_point :
    ∃ p : Spec (.of K) ⟶ space K,∀ s : Choice,
      ∃ z : Spec (.of K) ⟶ Spec (.of (MvPolynomial (Fin 6) K)),z ≫ chart K s=p := by
  let q := graphPresentation (Spec (.of K))
  let f := M9Native.MukaiLagrangianMap.classifying K (𝟙 (Spec (.of K))) q
  obtain ⟨e,he⟩ := M9Native.MukaiLagrangianMap.classifying_pullback_isomorphic
    K (𝟙 (Spec (.of K))) q
  have hkill : AnnihilatesSigma (Spec (.of K))
      (pullbackPresentation f (universalQuotient K)).map :=
    (annihilatesSigma_iff_of_iso _ _ _ e he).mpr (graphPresentation_annihilatesSigma _)
  obtain ⟨p,hp⟩ := (factorsThrough_iff_pullbackQuotient_annihilates K f).mpr hkill
  have he' : ∃ e' : (pullbackPresentation (p ≫ inclusion K) (universalQuotient K)).target ≅
      freeOn (Spec (.of K)) 3,
      (pullbackPresentation (p ≫ inclusion K) (universalQuotient K)).map ≫ e'.hom=q.map := by
    rw [hp]
    exact ⟨e,he⟩
  obtain ⟨e',he'⟩ := he'
  refine ⟨p,fun s => exists_chart_factor_of_isUnit_minor K p e' s ?_⟩
  rw [he',graphPresentation_matrix,graphMatrix_admissibleMinor]
  exact isUnit_one

/-- All eight actual open subsets contain one and the same scheme point. -/
theorem exists_point_in_all_charts : ∃ x : space K,∀ s : Choice,x ∈ Set.range (chart K s) := by
  obtain ⟨p,hp⟩ := exists_common_chart_point K
  refine ⟨p (IsLocalRing.closedPoint K),fun s => ?_⟩
  obtain ⟨z,hz⟩ := hp s
  refine ⟨z (IsLocalRing.closedPoint K),?_⟩
  exact congrArg (fun f : Spec (.of K) ⟶ space K => f (IsLocalRing.closedPoint K)) hz

theorem chart_range_irreducible (s : Choice) : IsIrreducible (Set.range (chart K s)) := by
  simpa only [Set.image_univ] using
    (IrreducibleSpace.isIrreducible_univ (Spec (.of (MvPolynomial (Fin 6) K)))).image
      (chart K s) (chart K s).continuous.continuousOn

instance space_irreducible : IrreducibleSpace (space K) := by
  obtain ⟨x,hx⟩ := exists_point_in_all_charts K
  exact irreducibleSpace_of_isOpen_cover (fun s : Choice => Set.range (chart K s))
    (fun s => (chart K s).isOpenEmbedding.isOpen_range)
    (chart_range_irreducible K) (charts_cover K) x hx

instance space_reduced : IsReduced (space K) := by
  have (s : (admissibleCover K).I₀) : IsReduced ((admissibleCover K).X s) := by
    change IsReduced (Spec (.of (MvPolynomial (Fin 6) K)))
    infer_instance
  exact IsReduced.of_openCover (space K) (admissibleCover K)

/-- The original dual-evaluation zero-ideal LG scheme is integral over every field. -/
instance space_integral : IsIntegral (space K) :=
  isIntegral_of_irreducibleSpace_of_isReduced (space K)

instance space_connected : ConnectedSpace (space K) := inferInstance

theorem affineSix_dimension :
    topologicalKrullDim (Spec (.of (MvPolynomial (Fin 6) K)))=(6 : WithBot ℕ∞) := by
  change topologicalKrullDim (PrimeSpectrum (MvPolynomial (Fin 6) K))=_
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,ringKrullDim_eq_zero_of_field K]
  norm_num

theorem chart_range_dimension (s : Choice) :
    topologicalKrullDim (Set.range (chart K s))=(6 : WithBot ℕ∞) := by
  let h := (chart K s).isOpenEmbedding.isEmbedding.toHomeomorph
  rw [← IsHomeomorph.topologicalKrullDim_eq h h.isHomeomorph,affineSix_dimension]

/-- The global topological Krull dimension of the actual LG scheme is six. -/
theorem space_dimension : topologicalKrullDim (space K)=(6 : WithBot ℕ∞) := by
  apply le_antisymm
  · exact topologicalKrullDim_le_of_isOpen_cover (fun s : Choice => Set.range (chart K s))
      (fun s => (chart K s).isOpenEmbedding.isOpen_range) (charts_cover K)
      (fun s => (chart_range_dimension K s).le)
  · have h := (bigCell K).isOpenEmbedding.isInducing.topologicalKrullDim_le
    rw [affineSix_dimension] at h
    exact h

instance projection_geometricallyIrreducible [IsSepClosed K] :
    GeometricallyIrreducible (projection K) :=
  geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed K (space K) (projection K)

instance projection_geometricallyIntegral [IsSepClosed K] [PerfectField K] :
    GeometricallyIntegral (projection K) :=
  GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _

/-- The finite cover also removes the algebraic-closure hypothesis from smoothness. -/
instance projection_smoothOfRelativeDimension : SmoothOfRelativeDimension 6 (projection K) := by
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension 6 : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P:=@SmoothOfRelativeDimension 6)
    (admissibleCover K) fun s => ?_
  change SmoothOfRelativeDimension 6 (chart K s ≫ projection K)
  rw [chart_projection]
  exact M9Native.LagrangianTranslatedCharts.polynomialSix_smoothOfRelativeDimension K

instance projection_smooth : Smooth (projection K) :=
  SmoothOfRelativeDimension.smooth 6 (projection K)

end Geometry

end M9Native.LagrangianIntegral

end
