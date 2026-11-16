module

public import M9StacksIntegration.LagrangianCommonKernelChartAlgebra
public import M9StacksIntegration.LagrangianCommonKernelZero
public import M9StacksIntegration.LagrangianTranslatedDeterminantSections
public import M9StacksIntegration.FiniteFreeSectionIdeal

/-! The original common-kernel zero scheme pulled to an actual
admissible chart is the actual first-column coordinate zero scheme. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite

universe u

namespace M9Native.LagrangianCommonKernelChartIdeal

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

open LagrangianGrassmannian LagrangianMatrixChart LagrangianPluckerQuotient
open LagrangianAdmissibleMinors LagrangianAdmissibleCharts LagrangianTransitivity
open LagrangianTranslatedDeterminantSections LagrangianIsotropicRestriction
open LagrangianCommonKernelZero LagrangianCommonKernelChartAlgebra
open FiniteFreeSectionIdeal SectionZeroIdealFactorization AlgebraicGeometry.Grassmannian

variable (K : Type u) [Field K] [CharZero K]

abbrev ChartRing := MvPolynomial (Fin 6) K
abbrev chartSpace : Scheme.{u} := Spec (.of (ChartRing K))

def quotientFrame (s : Choice) :
    (pullbackPresentation (chart K s) (quotientOnLG K)).target ≅ freeOn (chartSpace K) 3 :=
  translatedQuotientIso K (swap K s)⁻¹

def sectionPolynomials (s : Choice) : Fin 3 → ChartRing K :=
  (translatedMatrix K (swap K s)⁻¹).col 0

abbrev chartSection (s : Choice) :=
  pullbackGlobalSections (chart K s) (quotientOnLG K).target (standardSection K)

abbrev chartIdeal (s : Choice) := (zeroIdeal K).comap (chart K s)
abbrev chartZero (s : Choice) : Scheme.{u} := pullback (chart K s) (zeroInclusion K)

omit [CharZero K] in
theorem sectionPolynomials_eq (s : Choice) :
    sectionPolynomials K s =
      if s 0 then -(headVariable K) else Pi.single 0 1 := by
  change (MukaiConormalBigCellSections.graphQuotientMatrix K *
    matrixSix (ChartRing K) (mapSymplectic K MvPolynomial.C (swap K s)⁻¹)).col
      ((0 : Fin 3).castAdd 3) = _
  rw [product_mapped_swap_inverse_column]
  funext i
  by_cases hs : s 0
  · simp only [hs,ite_true,Pi.neg_apply]
    change -(LagrangianPluckerFirstJet.standard (ChartRing K)
      (MukaiConormalBigCellSections.graphMatrix K) i (Fin.natAdd 3 (0 : Fin 3))) =
        -(headVariable K i)
    rw [LagrangianPluckerFirstJet.standard_f]
    rfl
  · simp only [hs]
    change LagrangianPluckerFirstJet.standard (ChartRing K)
      (MukaiConormalBigCellSections.graphMatrix K) i ((0 : Fin 3).castAdd 3) =
        ((Pi.single (0 : Fin 3) (1 : ChartRing K)) : Fin 3 → ChartRing K) i
    rw [LagrangianPluckerFirstJet.standard_e]
    simp [Pi.single_apply]

theorem framedSection_coordinates (s : Choice) :
    freeSectionCoordinates (chartSpace K) 3
      ((quotientFrame K s).hom.app ⊤ (chartSection K s)) =
        fun i => (Scheme.ΓSpecIso (.of (ChartRing K))).inv (sectionPolynomials K s i) := by
  funext i
  have h := pulledQuotient_basis (chart K s) (quotientOnLG K).map (0 : Fin 6)
  change Scheme.Modules.Hom.app (pullbackPresentation (chart K s) (quotientOnLG K)).map ⊤
      (freeBasisSection (chartSpace K) 6 0) = chartSection K s at h
  rw [← h]
  change freeSectionCoordinates (chartSpace K) 3
    (Scheme.Modules.Hom.app
      ((pullbackPresentation (chart K s) (quotientOnLG K)).map ≫ (quotientFrame K s).hom)
      ⊤ (freeBasisSection (chartSpace K) 6 0)) i = _
  calc
    _ = Stacks.FreeSheafMatrix.toMatrix
        ((pullbackPresentation (chart K s) (quotientOnLG K)).map ≫
          (quotientFrame K s).hom) i 0 :=
      freeCoordinates_map_basis (X := chartSpace K) _ i (0 : Fin 6)
    _ = _ := by
      have hm := congrArg (fun M : Matrix (Fin 3) (Fin 6) Γ(chartSpace K,⊤) => M i 0)
        (translatedQuotientIso_matrix K (swap K s)⁻¹)
      exact hm

theorem framedSection_eq_coordinateSection (s : Choice) :
    (quotientFrame K s).hom.app ⊤ (chartSection K s) =
      coordinateSection (ChartRing K) 3 (sectionPolynomials K s) := by
  apply (freeSectionCoordinates (chartSpace K) 3).injective
  rw [framedSection_coordinates,coordinateSection,LinearEquiv.apply_symm_apply]

/-- Equality of actual native ideal sheaves, before passing to spectra. -/
theorem chartIdeal_eq_coordinateIdeal (s : Choice) :
    chartIdeal K s = coordinateIdeal (ChartRing K) 3 (sectionPolynomials K s) := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (quotientOnLG K).target 3 :=
    (quotientOnLG K).finiteLocallyFree
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback (chart K s)).obj (quotientOnLG K).target) 3 :=
    isFiniteLocallyFreeOfRank_pullback (chart K s) _ 3
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (pullbackPresentation (chart K s) (quotientOnLG K)).target 3 :=
    (pullbackPresentation (chart K s) (quotientOnLG K)).finiteLocallyFree
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (freeOn (chartSpace K) 3) 3 :=
    free_isFiniteLocallyFreeOfRank _ 3
  calc
    _ = SectionZeroIdealFactorization.sectionZeroIdeal (chartSpace K)
        ((Scheme.Modules.pullback (chart K s)).obj (quotientOnLG K).target)
        (chartSection K s) := by
      rw [chartIdeal,zeroIdeal_eq_evaluationIdeal]
      exact (sectionZeroIdeal_pullback (chart K s) (quotientOnLG K).target 3
        (standardSection K)).symm
    _ = SectionZeroIdealFactorization.sectionZeroIdeal (chartSpace K) (freeOn (chartSpace K) 3)
        ((quotientFrame K s).hom.app ⊤ (chartSection K s)) :=
      sectionZeroIdeal_eq_of_iso 3 (quotientFrame K s) (chartSection K s)
    _ = _ := by rw [framedSection_eq_coordinateSection]; rfl

def chartZeroIsoCoordinate (s : Choice) :
    chartZero K s ≅ (coordinateIdeal (ChartRing K) 3 (sectionPolynomials K s)).subscheme :=
  ((zeroIdeal K).comapIso (chart K s)).symm ≪≫
    eqToIso (congrArg (fun I : (chartSpace K).IdealSheafData => I.subscheme)
      (chartIdeal_eq_coordinateIdeal K s))

def chartZeroIsoQuotient (s : Choice) :
    chartZero K s ≅ Spec (.of (ChartRing K ⧸ Ideal.span (Set.range (sectionPolynomials K s)))) :=
  chartZeroIsoCoordinate K s ≪≫
    coordinateZeroSchemeIsoQuotient (ChartRing K) 3 (sectionPolynomials K s)

@[reassoc] theorem chartZeroIsoQuotient_hom_inclusion (s : Choice) :
    (chartZeroIsoQuotient K s).hom ≫ quotientInclusion (ChartRing K) 3 (sectionPolynomials K s) =
      pullback.fst (chart K s) (zeroInclusion K) := by
  rw [chartZeroIsoQuotient,Iso.trans_hom,Category.assoc,
    coordinateZeroSchemeIsoQuotient_hom_inclusion]
  rw [chartZeroIsoCoordinate,Iso.trans_hom,Category.assoc,
    eqToIso_subscheme_ι _ _ (chartIdeal_eq_coordinateIdeal K s)]
  exact (zeroIdeal K).comapIso_inv_subschemeι (chart K s)

omit [CharZero K] in
theorem span_sectionPolynomials_false (s : Choice) (hs : s 0 = false) :
    Ideal.span (Set.range (sectionPolynomials K s)) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  apply Ideal.subset_span
  refine ⟨0,?_⟩
  simp [sectionPolynomials_eq,hs]

omit [CharZero K] in
theorem span_sectionPolynomials_true (s : Choice) (hs : s 0 = true) :
    Ideal.span (Set.range (sectionPolynomials K s)) = headIdeal K := by
  rw [sectionPolynomials_eq,ite_eq_left hs]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Submodule.neg_mem _ (Ideal.subset_span ⟨i,rfl⟩)
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have h : -(headVariable K i) ∈ Ideal.span (Set.range (-(headVariable K))) :=
      Ideal.subset_span ⟨i,rfl⟩
    have hn := Submodule.neg_mem (Ideal.span (Set.range (-(headVariable K)))) h
    change -(-(headVariable K i)) ∈ Ideal.span (Set.range (-(headVariable K))) at hn
    rw [neg_neg] at hn
    exact hn

end M9Native.LagrangianCommonKernelChartIdeal
