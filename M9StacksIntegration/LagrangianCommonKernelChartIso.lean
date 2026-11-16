module

public import M9StacksIntegration.LagrangianCommonKernelChartIdeal
public import M9StacksIntegration.LineFramePullback

/-! Actual local scheme isomorphisms for the original common-kernel
zero scheme: empty on four admissible charts and affine three-space on
the other four. The maps retain the original determinant coordinates. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option Elab.async false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite

universe u

namespace M9Native.LagrangianCommonKernelChartIso

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianAdmissibleMinors
open LagrangianAdmissibleCharts LagrangianCommonKernelZero LagrangianCommonKernelChartAlgebra
open LagrangianCommonKernelChartIdeal LagrangianTranslatedDeterminantSections

variable (K : Type u) [Field K] [CharZero K]

theorem chartZero_isEmpty (s : Choice) (hs : s 0 = false) : IsEmpty (chartZero K s) := by
  let A := ChartRing K ⧸ Ideal.span (Set.range (sectionPolynomials K s))
  have hA : Subsingleton A := by
    dsimp [A]
    rw [span_sectionPolynomials_false K s hs]
    infer_instance
  have hSpec : IsEmpty (Spec (.of A)) := by
    change IsEmpty (PrimeSpectrum A)
    exact PrimeSpectrum.isEmpty_iff_subsingleton.mpr hA
  exact ⟨fun x => hSpec.false ((chartZeroIsoQuotient K s).hom x)⟩

def chartRingEquiv (s : Choice) (hs : s 0 = true) :
    (ChartRing K ⧸ Ideal.span (Set.range (sectionPolynomials K s))) ≃ₐ[K]
      MvPolynomial (Fin 3) K :=
  (Ideal.quotientEquivAlgOfEq K (span_sectionPolynomials_true K s hs)).trans
    (quotientAffineThreeEquiv K)

omit [CharZero K] in
theorem chartRingEquiv_mk (s : Choice) (hs : s 0 = true) (p : ChartRing K) :
    chartRingEquiv K s hs
      (Ideal.Quotient.mk (Ideal.span (Set.range (sectionPolynomials K s))) p) =
        eraseHeadThree K p := by
  rw [chartRingEquiv,AlgEquiv.trans_apply,Ideal.quotientEquivAlgOfEq_mk,
    quotientAffineThreeEquiv_mk]

/-- The actual original local zero scheme is an actual affine-three
spectrum, not just its reduced space or a set of field points. -/
def chartZeroIsoAffineThree (s : Choice) (hs : s 0 = true) :
    chartZero K s ≅ Spec (.of (MvPolynomial (Fin 3) K)) :=
  chartZeroIsoQuotient K s ≪≫
    (Scheme.Spec.mapIso (chartRingEquiv K s hs).toRingEquiv.toCommRingCatIso.op).symm

theorem chartZeroIsoQuotient_inv_fst (s : Choice) :
    (chartZeroIsoQuotient K s).inv ≫ pullback.fst (chart K s) (zeroInclusion K) =
      FiniteFreeSectionIdeal.quotientInclusion (ChartRing K) 3 (sectionPolynomials K s) := by
  rw [← chartZeroIsoQuotient_hom_inclusion,Iso.inv_hom_id_assoc]

/-- The retained actual chart inclusion is the literal polynomial map
which kills the first symmetric row and column. -/
@[reassoc] theorem chartZeroIsoAffineThree_inv_fst (s : Choice) (hs : s 0 = true) :
    (chartZeroIsoAffineThree K s hs).inv ≫ pullback.fst (chart K s) (zeroInclusion K) =
      Spec.map (CommRingCat.ofHom (eraseHeadThree K).toRingHom) := by
  rw [chartZeroIsoAffineThree,Iso.trans_inv,Category.assoc,chartZeroIsoQuotient_inv_fst]
  change Spec.map (CommRingCat.ofHom (chartRingEquiv K s hs).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span (Set.range (sectionPolynomials K s))))) = _
  rw [← Spec.map_comp]
  congr 1

def affineThreeMap (s : Choice) (hs : s 0 = true) :
    Spec (.of (MvPolynomial (Fin 3) K)) ⟶ zeroSpace K :=
  (chartZeroIsoAffineThree K s hs).inv ≫ pullback.snd (chart K s) (zeroInclusion K)

instance affineThreeMap_isOpenImmersion (s : Choice) (hs : s 0 = true) :
    IsOpenImmersion (affineThreeMap K s hs) := by
  dsimp [affineThreeMap]
  infer_instance

@[reassoc] theorem affineThreeMap_inclusion (s : Choice) (hs : s 0 = true) :
    affineThreeMap K s hs ≫ zeroInclusion K =
      Spec.map (CommRingCat.ofHom (eraseHeadThree K).toRingHom) ≫ chart K s := by
  rw [affineThreeMap,Category.assoc,← pullback.condition,← Category.assoc,
    chartZeroIsoAffineThree_inv_fst]

@[reassoc] theorem affineThreeMap_projection (s : Choice) (hs : s 0 = true) :
    affineThreeMap K s hs ≫ zeroProjection K =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K)) := by
  rw [zeroProjection,← Category.assoc,affineThreeMap_inclusion,Category.assoc,chart_projection]
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun c => (eraseHeadThree K).commutes c)

theorem affineThreeMap_range (s : Choice) (hs : s 0 = true) :
    Set.range (affineThreeMap K s hs) =
      Set.range (pullback.snd (chart K s) (zeroInclusion K)) := by
  change Set.range (Function.comp (pullback.snd (chart K s) (zeroInclusion K))
    (chartZeroIsoAffineThree K s hs).inv) = _
  rw [Set.range_comp,Set.range_eq_univ.mpr (chartZeroIsoAffineThree K s hs).inv.surjective,
    Set.image_univ]

/-- The original eight-chart cover restricts to the four actual
affine-three charts of the native common-kernel zero scheme. -/
theorem affineThreeMaps_cover (x : zeroSpace K) :
    ∃ (s : Choice) (hs : s 0 = true), x ∈ Set.range (affineThreeMap K s hs) := by
  obtain ⟨s,hx⟩ := charts_cover K (zeroInclusion K x)
  have hr : x ∈ Set.range (pullback.snd (chart K s) (zeroInclusion K)) := by
    rw [Scheme.Pullback.range_snd]
    exact hx
  cases hs : s 0 with
  | false =>
    let : IsEmpty (chartZero K s) := chartZero_isEmpty K s hs
    obtain ⟨y,_⟩ := hr
    exact isEmptyElim y
  | true =>
    refine ⟨s,hs,?_⟩
    rw [affineThreeMap_range]
    exact hr

abbrev SurvivingChoice := {s : Choice // s 0 = true}

def survivingChoiceEquiv : SurvivingChoice ≃ (Fin 2 → Bool) where
  toFun s i := s.val i.succ
  invFun t := ⟨Fin.cases true t,rfl⟩
  left_inv s := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    exact s.property.symm
  right_inv _ := rfl

theorem card_survivingChoice : Fintype.card SurvivingChoice = 4 := by
  rw [Fintype.card_congr survivingChoiceEquiv,Fintype.card_fun]
  decide

def affineThreeCover : (zeroSpace K).OpenCover :=
  Scheme.Cover.mkOfCovers SurvivingChoice
    (fun _ => Spec (.of (MvPolynomial (Fin 3) K)))
    (fun s => affineThreeMap K s.val s.property)
    (fun x => by
      obtain ⟨s,hs,y,hy⟩ := affineThreeMaps_cover K x
      exact ⟨⟨s,hs⟩,y,hy⟩)

abbrev tailMap : Spec (.of (MvPolynomial (Fin 3) K)) ⟶ chartSpace K :=
  Spec.map (CommRingCat.ofHom (eraseHeadThree K).toRingHom)

abbrev affineLGMap (s : Choice) := tailMap K ≫ chart K s

omit [CharZero K] in
theorem tailMap_scalar (p : ChartRing K) :
    (tailMap K).appTop ((Scheme.ΓSpecIso (.of (ChartRing K))).inv p) =
      (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 3) K))).inv (eraseHeadThree K p) := by
  change (Spec.map (CommRingCat.ofHom (eraseHeadThree K).toRingHom)).appTop
    ((Scheme.ΓSpecIso (.of (ChartRing K))).inv p) = _
  rw [← CommRingCat.comp_apply,← Scheme.ΓSpecIso_inv_naturality,CommRingCat.comp_apply]
  rfl

/-- The original determinant frame is pulled by the literal tail map;
no frame or projective-coordinate normalization is supplied. -/
def determinantFrame (s : Choice) :
    (Scheme.Modules.pullback (affineLGMap K s)).obj (determinantLine K) ≅
      SheafOfModules.unit (Spec (.of (MvPolynomial (Fin 3) K))).ringCatSheaf :=
  ((Scheme.Modules.pullbackComp (tailMap K) (chart K s)).app (determinantLine K)).symm ≪≫
    LineFramePullback.pullbackFrame (tailMap K)
      ((Scheme.Modules.pullback (chart K s)).obj (determinantLine K))
      (translatedDeterminantIso K (swap K s)⁻¹)

/-- All original primitive coordinates survive the actual local scheme
isomorphism through the explicit polynomial specialization. -/
theorem determinantFrame_coordinate (s : Choice) (j : Fin 14) :
    (determinantFrame K s).hom.app ⊤
      (pullbackGlobalSections (affineLGMap K s) (determinantLine K) (primitiveSections K j)) =
        (Scheme.ΓSpecIso (.of (MvPolynomial (Fin 3) K))).inv
          (eraseHeadThree K (translatedPolynomial K (swap K s)⁻¹ j)) := by
  change LinearIncidenceTensorCoordinates.unitCoordinate _
    ((LineFramePullback.pullbackFrame (tailMap K)
      ((Scheme.Modules.pullback (chart K s)).obj (determinantLine K))
      (translatedDeterminantIso K (swap K s)⁻¹)).hom.app ⊤
        (((Scheme.Modules.pullbackComp (tailMap K) (chart K s)).inv.app
          (determinantLine K)).app ⊤
            (pullbackGlobalSections (affineLGMap K s) (determinantLine K)
              (primitiveSections K j)))) = _
  rw [LineFramePullback.pullbackComp_inv_apply,
    LineFramePullback.pullbackFrame_coordinate]
  calc
    _ = (tailMap K).appTop (MukaiConormalBigCellSections.scalarEquiv K
        (translatedPolynomial K (swap K s)⁻¹ j)) :=
      congrArg (fun r : Γ(chartSpace K,⊤) => (tailMap K).appTop r)
        (translatedDeterminantIso_coordinate K (swap K s)⁻¹ j)
    _ = _ := tailMap_scalar K _

end M9Native.LagrangianCommonKernelChartIso
