module

public import M9StacksIntegration.MukaiConormalRowPointFrame
public import M9StacksIntegration.LagrangianFixedEquationRows
public import M9StacksIntegration.FieldPointDualPairing
public import M9StacksIntegration.OpenPullbackFunctional
public import M9StacksIntegration.MukaiFramedSectionSum
public import M9StacksIntegration.UnitSectionsLinearMap

/-!
# The original row-to-conormal map in actual translated point coordinates

The actual point source frame and actual conormal map are retained.
Original fibre containment gives literal original-row vanishing. Values
and differentials are compared in the genuine translated determinant
frame and native field-point cotangent modules.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
open scoped BigOperators

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  SheafOfModules.unit PresheafOfModules.unit AlgebraicGeometry.SheafedSpace.sheaf

universe u
namespace M9Native.MukaiConormalRowFirstJet

open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianMatrixChart
open MukaiConormalChartJets LagrangianTranslatedCharts LagrangianTranslatedDeterminantSections
open MukaiConormalChartCovariance MukaiConormalOriginCoordinates LagrangianFieldJetCoefficients

variable (K : Type u) [Field K] [CharZero K] {X : Scheme.{u}}
  (i : X ⟶ space K) (p : Spec (.of K) ⟶ X)
  (g : Matrix.symplecticGroup (Fin 3) K) (z : Spec (.of K) ⟶ chart K)
  (hz : z ≫ translatedBigCell K g = p ≫ i)

/-- The source normalization is constructed from the actual translated frame. -/
abbrev pointSourceEquiv := MukaiConormalRowPointFrame.pointSourceEquiv K i p g z hz

variable (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  (q : X ⟶ LagrangianFibreFactorization.fibre K
    (LagrangianMatrixPointRows.matrixPoint K M hM))
  (hq : q ≫ LagrangianFibreFactorization.fibreToLG K
    (LagrangianMatrixPointRows.matrixPoint K M hM) = i)

/-- The genuine original conormal map at the actual point, in the derived five-row coordinates. -/
def pointSequenceMap (K : Type u) [Field K] [CharZero K] {X : Scheme.{u}}
    (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
    (i : X ⟶ space K) [IsClosedImmersion i]
    (q : X ⟶ LagrangianFibreFactorization.fibre K
      (LagrangianMatrixPointRows.matrixPoint K M hM))
    (hq : q ≫ LagrangianFibreFactorization.fibreToLG K
      (LagrangianMatrixPointRows.matrixPoint K M hM) = i)
    (p : Spec (.of K) ⟶ X) (g : Matrix.symplecticGroup (Fin 3) K)
    (z : Spec (.of K) ⟶ chart K) (hz : z ≫ translatedBigCell K g = p ≫ i) : (Fin 5 → K) →ₗ[K]
    moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj
      (LagrangianCurveConormal.sequence K i).X₁) :=
  (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
    (LagrangianFibreConormalMap.sequenceMap K M hM i q hq))).hom.comp
      (pointSourceEquiv K i p g z hz).symm.toLinearMap

include q hq in
/-- Every literal original row vanishes along the actual original source. -/
theorem original_row_pullback_zero (a : Fin 5 → K) :
    pullbackGlobalSections i (determinantLine K)
      (LagrangianHyperplaneCoordinates.determinantSection K (Matrix.vecMul a M)) = 0 := by
  rw [← LagrangianFixedEquationRows.rowProjection_fiveSection K M hM a]
  rw [← SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections,
    LagrangianFibreConormalMap.pullback_fiveSection_eq_zero K M hM i q hq, map_zero]

/-- Literal original hyperplane coordinates in the actual translated determinant frame. -/
def framedSection (g : Matrix.symplecticGroup (Fin 3) K) (c : Fin 14 → K) : Γ(chart K, ⊤) :=
  (translatedDeterminantIso K g).hom.app ⊤
    (pullbackGlobalSections (translatedBigCell K g) (determinantLine K)
      (LagrangianHyperplaneCoordinates.determinantSection K c))

private theorem framedSection_sum_pullback (g : Matrix.symplecticGroup (Fin 3) K) (c : Fin 14 → K) :
    MukaiFramedSectionSum.framedPullback (translatedBigCell K g) (determinantLine K)
      (translatedDeterminantIso K g)
      (∑ j : Fin 14, LagrangianHyperplaneCoordinates.coefficientMap K (c j) • primitiveSections K j) =
      ∑ j : Fin 14, (translatedBigCell K g).appTop
        (LagrangianHyperplaneCoordinates.coefficientMap K (c j)) *
        MukaiFramedSectionSum.framedPullback (translatedBigCell K g) (determinantLine K)
          (translatedDeterminantIso K g) (primitiveSections K j) := by
  let T := UnitSectionsLinearMap.toRing
    ((Scheme.Modules.pullback (translatedBigCell K g)).obj (determinantLine K))
    (translatedDeterminantIso K g).hom
  change T (pullbackGlobalSections (translatedBigCell K g) (determinantLine K)
      (∑ j : Fin 14, LagrangianHyperplaneCoordinates.coefficientMap K (c j) • primitiveSections K j)) =
    ∑ j : Fin 14, (translatedBigCell K g).appTop
      (LagrangianHyperplaneCoordinates.coefficientMap K (c j)) *
        T (pullbackGlobalSections (translatedBigCell K g) (determinantLine K) (primitiveSections K j))
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [SectionsEqualizer.pullbackGlobalSections_smul]
  exact T.map_smul _ _

private theorem framedSection_eq_framedPullback (g : Matrix.symplecticGroup (Fin 3) K) (c : Fin 14 → K) :
    framedSection K g c =
      MukaiFramedSectionSum.framedPullback (translatedBigCell K g) (determinantLine K)
        (translatedDeterminantIso K g)
        (∑ j : Fin 14, LagrangianHyperplaneCoordinates.coefficientMap K (c j) • primitiveSections K j) := rfl

private theorem coefficient_pullback_apply {Y Z : Scheme.{u}}
    (f : Y ⟶ space K) (t : Z ⟶ Y) (c : K) :
    t.appTop (LagrangianPlucker.coefficientMap K f c) =
      LagrangianPlucker.coefficientMap K (t ≫ f) c :=
  (RingHom.congr_fun (LagrangianPlucker.coefficientMap_comp K f t) c).symm

private theorem coefficient_pullback_id_apply {Y : Scheme.{u}} (t : Y ⟶ space K) (c : K) :
    t.appTop (LagrangianHyperplaneCoordinates.coefficientMap K c) =
      LagrangianPlucker.coefficientMap K t c := by
  simpa only [Category.comp_id] using
    coefficient_pullback_apply K (𝟙 (space K)) t c

private theorem translated_coefficient_pullback (g : Matrix.symplecticGroup (Fin 3) K) (c : K) :
    (translatedBigCell K g).appTop (LagrangianHyperplaneCoordinates.coefficientMap K c) =
      LagrangianPlucker.coefficientMap K (translatedBigCell K g) c :=
  coefficient_pullback_id_apply K (translatedBigCell K g) c

private theorem translated_coefficient_action (g : Matrix.symplecticGroup (Fin 3) K) :
    LagrangianPlucker.coefficientMap K (translatedBigCell K g) =
      (MukaiConormalBigCellSections.scalarEquiv K).toRingHom.comp MvPolynomial.C :=
  (LagrangianDeterminantAction.coefficientMap_action K (LagrangianMatrixChart.bigCell K) g).trans
    (MukaiConormalBigCellSections.bigCell_coefficientMap K)

private theorem chart_coefficient_scalar (c : K) :
    MukaiConormalBigCellSections.scalarEquiv K (MvPolynomial.C c) =
      LagrangianSymplecticAction.scalarMap K (chartProjection K) c :=
  (MukaiConormalChartCovariance.chart_scalar K c).symm

private theorem translated_coefficient_eq (g : Matrix.symplecticGroup (Fin 3) K) (c : K) :
    (translatedBigCell K g).appTop (LagrangianHyperplaneCoordinates.coefficientMap K c) =
      LagrangianSymplecticAction.scalarMap K (chartProjection K) c := by
  exact (translated_coefficient_pullback K g c).trans
    ((RingHom.congr_fun (translated_coefficient_action K g) c).trans
      (chart_coefficient_scalar K c))

private theorem sectionTuple_eq_framedPullback (g : Matrix.symplecticGroup (Fin 3) K) (j : Fin 14) :
    MukaiFramedSectionSum.framedPullback (translatedBigCell K g) (determinantLine K)
      (translatedDeterminantIso K g) (primitiveSections K j) = sectionTuple K g j := rfl

theorem framedSection_eq (g : Matrix.symplecticGroup (Fin 3) K) (c : Fin 14 → K) :
    framedSection K g c = ∑ j : Fin 14,
      LagrangianSymplecticAction.scalarMap K (chartProjection K) (c j) * sectionTuple K g j := by
  rw [framedSection_eq_framedPullback, framedSection_sum_pullback]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg₂ (· * ·) (translated_coefficient_eq K g (c j)) (sectionTuple_eq_framedPullback K g j)


include hz in
/-- The original base-point triangle derives the actual chart-point base identity. -/
theorem chart_point_overBase (hp : p ≫ (i ≫ projection K) = 𝟙 _) :
    z ≫ chartProjection K = 𝟙 _ := by
  have hb : translatedBigCell K g ≫ projection K = chartProjection K :=
    translatedBigCell_projection K g
  calc
    _ = z ≫ (translatedBigCell K g ≫ projection K) := by rw [hb]
    _ = (z ≫ translatedBigCell K g) ≫ projection K := (Category.assoc _ _ _).symm
    _ = (p ≫ i) ≫ projection K := by rw [hz]
    _ = 𝟙 _ := (Category.assoc _ _ _).trans hp

include q hq hz in
/-- Fibre containment gives the value part of the FULL LG jet, with the original row coefficients. -/
theorem original_row_value_zero (hp : p ≫ (i ≫ projection K) = 𝟙 _) (a : Fin 5 → K) :
    valueMap K z (sectionTuple K g) ((formsCoordinates K).symm (Matrix.vecMul a M)) = 0 := by
  have hrow := original_row_pullback_zero K i M hM q hq a
  have hpoint := congrArg (fun s =>
    (MukaiConormalRowPointFrame.pointLineFrame K i p g z hz).hom.app ⊤
      (pullbackGlobalSections p ((Scheme.Modules.pullback i).obj (determinantLine K)) s)) hrow
  have hframe := LineFramePullback.squareFrame_coordinate p i z (translatedBigCell K g) hz.symm
    (determinantLine K) (translatedDeterminantIso K g)
    (LagrangianHyperplaneCoordinates.determinantSection K (Matrix.vecMul a M))
  have hzero : z.appTop (framedSection K g (Matrix.vecMul a M)) = 0 := by
    simpa only [MukaiConormalRowPointFrame.pointLineFrame, framedSection,
      LinearIncidenceTensorCoordinates.unitCoordinate, map_zero] using
      hframe.symm.trans hpoint
  have hvalue := congrArg ((Scheme.ΓSpecIso (.of K)).hom) hzero
  simp only [map_zero] at hvalue
  rw [framedSection_eq] at hvalue
  change pointValue K z (∑ j : Fin 14,
      LagrangianSymplecticAction.scalarMap K (chartProjection K) ((Matrix.vecMul a M) j) *
        sectionTuple K g j) = 0 at hvalue
  rw [pointValue_sum_constants K (chartProjection K) z
    (chart_point_overBase K i p g z hz hp)] at hvalue
  simpa only [valueMap, LinearMap.coe_mk, AddHom.coe_mk, formsCoordinates_symm_basis, MukaiConormalChartJets.value,
    LagrangianFieldJetCoefficients.pointValue] using hvalue

/-- The actual local equation-dual row is evaluation of the actual original row section. -/
theorem row_evaluation_eq (a : Fin 5 → K) (U : (space K).Opens)
    (τ : Γ(dualSheaf (determinantLine K), U)) :
    evalAt (LagrangianFiveSectionModel.equationBundle K)
      ((dualMap (LagrangianRowDifferential.rowProjection K a)).app U τ)
      ((LagrangianFiveSectionModel.equationBundle K).presheaf.map (homOfLE le_top).op
        (LagrangianFibreFiveSection.fiveSection K M hM)) =
      evalAt (determinantLine K) τ
        ((determinantLine K).presheaf.map (homOfLE le_top).op
          (LagrangianHyperplaneCoordinates.determinantSection K (Matrix.vecMul a M))) := by
  rw [← LagrangianFixedEquationRows.rowProjection_fiveSection K M hM a]
  exact (dualPairing_dualMap (LagrangianRowDifferential.rowProjection K a) τ
    (Over.mk (𝟙 U)) _).trans
      (congrArg (evalAt (determinantLine K) τ)
        (PresheafOfModules.naturality_apply (LagrangianRowDifferential.rowProjection K a).val
          (homOfLE le_top).op (LagrangianFibreFiveSection.fiveSection K M hM)))

/-- The original local functional is pulled through the original immersion and point units. -/
def localRowInput (U : (space K).Opens)
    (hU : (p ≫ i).base (SpecFieldStalkSections.point K) ∈ U)
    (τ : Γ(dualSheaf (determinantLine K), U)) (a : Fin 5 → K) :
    MukaiConormalRowPointFrame.PointSource K i p :=
  SpecFieldPullbackSections.pulledSection K p (LagrangianFibreConormalMap.source K i)
    (i ⁻¹ᵁ U) hU
    (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
      (dualSheaf (LagrangianFiveSectionModel.equationBundle K))).app U
      ((dualMap (LagrangianRowDifferential.rowProjection K a)).app U τ))

/-- The literal base scalar restricted to an original ambient open. -/
def localScalar (U : (space K).Opens) (c : K) : Γ(space K,U) :=
  (space K).presheaf.map (homOfLE le_top).op
    (LagrangianSymplecticAction.scalarMap K (projection K) c)

omit [CharZero K] in
theorem localScalar_eq_baseRingToSections (U : (space K).Opens) (c : K) :
    localScalar K U c = (show Γ(space K,U) from baseRingToSections K (Over.mk (projection K)) (op U) c) := rfl

omit [CharZero K] in
theorem localScalar_map {U V : (space K).Opens} (v : V ⟶ U) (c : K) :
    (space K).presheaf.map v.op (localScalar K U c) = localScalar K V c := by
  unfold localScalar
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp]
  rfl

/-- Evaluation at any original slice object is additive in an actual local dual section. -/
def pairingAddHom {A : Scheme.{u}} (F : A.Modules) (U : A.Opens)
    (W : Over U) (y : Γ(F,W.left)) : Γ(dualSheaf F,U) →+ Γ(A,W.left) where
  toFun τ := dualPairing F τ W y
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The original row dual retains the literal five original coefficients on every open. -/
theorem rowDual_app_eq_sum (a : Fin 5 → K) (U : (space K).Opens)
    (τ : Γ(dualSheaf (determinantLine K),U)) :
    (dualMap (LagrangianRowDifferential.rowProjection K a)).app U τ =
      ∑ j : Fin 5, localScalar K U (a j) •
        (dualMap (TensorFreeCoordinates.projection (space K) (determinantLine K) 5 (ULift.up j))).app U τ := by
  apply dualPairing_ext
  intro W y
  have hs := map_sum
    (pairingAddHom (LagrangianFiveSectionModel.equationBundle K) U W y)
    (fun j : Fin 5 => localScalar K U (a j) •
      (dualMap (TensorFreeCoordinates.projection (space K) (determinantLine K) 5 (ULift.up j))).app U τ)
    Finset.univ
  change dualPairing (LagrangianFiveSectionModel.equationBundle K)
      (∑ j : Fin 5, localScalar K U (a j) •
        (dualMap (TensorFreeCoordinates.projection (space K) (determinantLine K) 5 (ULift.up j))).app U τ) W y =
    ∑ j : Fin 5, dualPairing (LagrangianFiveSectionModel.equationBundle K)
      (localScalar K U (a j) •
        (dualMap (TensorFreeCoordinates.projection (space K) (determinantLine K) 5 (ULift.up j))).app U τ) W y at hs
  rw [dualPairing_dualMap, hs]
  change (τ.app (op W)).hom ((LagrangianRowDifferential.rowProjection K a).app W.left y) = _
  rw [LagrangianRowDifferential.rowProjection, TensorFreeRowProjection.row_app]
  simp only [map_sum, map_smul, dualPairing_smul, localScalar_map, dualPairing_dualMap,
    ← localScalar_eq_baseRingToSections, smul_eq_mul]
  rfl

/-- Pullback of a local section over the full preimage is its literal adjunction unit. -/
theorem pullbackSection_preimage {A B : Scheme.{u}} (f : A ⟶ B) (N : B.Modules)
    (U : B.Opens) (t : Γ(N,U)) :
    Scheme.Modules.pullbackSection f N U (f ⁻¹ᵁ U) le_rfl t =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).app U t := by
  change ((Scheme.Modules.pullback f).obj N).presheaf.map (𝟙 (op (f ⁻¹ᵁ U))) _ = _
  exact CategoryTheory.Functor.map_id_apply
    ((Scheme.Modules.pullback f).obj N).presheaf (op (f ⁻¹ᵁ U)) _

/-- Actual local section pullback is semilinear for the original appLE ring map. -/
def pointLocalPullback {A : Scheme.{u}} (t : Spec (.of K) ⟶ A) (F : A.Modules)
    (U : A.Opens) (hU : t.base (SpecFieldStalkSections.point K) ∈ U) :
    Γ(F,U) →ₛₗ[(t.appLE U ⊤ (SpecFieldPullbackSections.preimageTop K t U hU)).hom]
      Γ((Scheme.Modules.pullback t).obj F,⊤) where
  toFun := SpecFieldPullbackSections.pulledSection K t F U hU
  map_add' a b := by
    let ηm := (((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app F).val.app (op U)).hom
    let ρm := (((Scheme.Modules.pullback t).obj F).val.map
      (homOfLE (SpecFieldPullbackSections.preimageTop K t U hU)).op).hom
    let η : Γ(F,U) → Γ((Scheme.Modules.pullback t).obj F,t ⁻¹ᵁ U) := ηm
    let ρ : Γ((Scheme.Modules.pullback t).obj F,t ⁻¹ᵁ U) →
        Γ((Scheme.Modules.pullback t).obj F,⊤) := ρm
    change ρ (η (a+b)) = ρ (η a) + ρ (η b)
    exact (congrArg ρ (ηm.map_add a b)).trans (ρm.map_add _ _)
  map_smul' c a := by
    let ηm := (((Scheme.Modules.pullbackPushforwardAdjunction t).unit.app F).val.app (op U)).hom
    let ρm := (((Scheme.Modules.pullback t).obj F).val.map
      (homOfLE (SpecFieldPullbackSections.preimageTop K t U hU)).op).hom
    let η : Γ(F,U) → Γ((Scheme.Modules.pullback t).obj F,t ⁻¹ᵁ U) := ηm
    let ρ : Γ((Scheme.Modules.pullback t).obj F,t ⁻¹ᵁ U) →
        Γ((Scheme.Modules.pullback t).obj F,⊤) := ρm
    have hη : η (c • a) = (t.app U).hom c • η a := ηm.map_smul c a
    change ρ (η (c • a)) = _
    rw [hη]
    exact ρm.map_smul ((t.app U).hom c) (η a)

/-- The identity base triangle gives the literal original K scalar after local point pullback. -/
theorem localScalar_point (hp : p ≫ (i ≫ projection K) = 𝟙 _)
    (U : (space K).Opens) (hU : (p ≫ i).base (SpecFieldStalkSections.point K) ∈ U) (c : K) :
    (p ≫ i).appLE U ⊤ (SpecFieldPullbackSections.preimageTop K (p ≫ i) U hU)
      (localScalar K U c) = (Scheme.ΓSpecIso (.of K)).inv c := by
  have h := congrArg (fun t => t.hom (LagrangianSymplecticAction.scalarMap K (projection K) c))
    ((p ≫ i).map_appLE (SpecFieldPullbackSections.preimageTop K (p ≫ i) U hU)
      (homOfLE (show U ≤ ⊤ from le_top)).op)
  change (p ≫ i).appLE U ⊤ _ (localScalar K U c) =
    (p ≫ i).appLE ⊤ ⊤ _ (LagrangianSymplecticAction.scalarMap K (projection K) c) at h
  have happ : (p ≫ i).appLE ⊤ ⊤ (by simp) = (p ≫ i).appTop := by
    have hm : (Spec (.of K)).presheaf.map
        (homOfLE (show (⊤ : (Spec (.of K)).Opens) ≤ (p ≫ i) ⁻¹ᵁ ⊤ by simp)).op =
          𝟙 Γ(Spec (.of K),⊤) := by
      change (Spec (.of K)).presheaf.map (𝟙 (op (⊤ : (Spec (.of K)).Opens))) = _
      exact (Spec (.of K)).presheaf.map_id _
    rw [Scheme.Hom.appLE, hm]
    exact Category.comp_id _
  rw [happ] at h
  exact h.trans (LagrangianFieldJetCoefficients.scalar_pullback K (projection K) (p ≫ i)
    (by simpa only [Category.assoc] using hp) c)

/-- The two actual pullback units coincide with the original composite unit on local rows. -/
theorem localRowInput_eq_composite (U : (space K).Opens)
    (hU : (p ≫ i).base (SpecFieldStalkSections.point K) ∈ U)
    (τ : Γ(dualSheaf (determinantLine K), U)) (a : Fin 5 → K) :
    localRowInput K i p U hU τ a =
      ((Scheme.Modules.pullbackComp p i).app
        (dualSheaf (LagrangianFiveSectionModel.equationBundle K))).inv.app ⊤
        (SpecFieldPullbackSections.pulledSection K (p ≫ i)
          (dualSheaf (LagrangianFiveSectionModel.equationBundle K)) U hU
          ((dualMap (LagrangianRowDifferential.rowProjection K a)).app U τ)) := by
  let F := dualSheaf (LagrangianFiveSectionModel.equationBundle K)
  let l := (moduleSpecΓFunctor.mapIso ((Scheme.Modules.pullbackComp p i).app F)).toLinearEquiv
  change localRowInput K i p U hU τ a = l.symm _
  apply l.injective
  rw [LinearEquiv.apply_symm_apply]
  have h := Scheme.Modules.pullbackSection_comp p i F U (i ⁻¹ᵁ U) ⊤ le_rfl
    (SpecFieldPullbackSections.preimageTop K p (i ⁻¹ᵁ U) hU)
    (SpecFieldPullbackSections.preimageTop K (p ≫ i) U hU)
    ((dualMap (LagrangianRowDifferential.rowProjection K a)).app U τ)
  rw [pullbackSection_preimage] at h
  exact h

/-- The genuine original local-row source is K-linear in all five row coefficients. -/
theorem localRowInput_eq_sum (hp : p ≫ (i ≫ projection K) = 𝟙 _)
    (U : (space K).Opens) (hU : (p ≫ i).base (SpecFieldStalkSections.point K) ∈ U)
    (τ : Γ(dualSheaf (determinantLine K), U)) (a : Fin 5 → K) :
    localRowInput K i p U hU τ a =
      ∑ j : Fin 5, a j • localRowInput K i p U hU τ (Pi.single j 1) := by
  classical
  have hsingle (j : Fin 5) : LagrangianRowDifferential.rowProjection K (Pi.single j 1) =
      TensorFreeCoordinates.projection (space K) (determinantLine K) 5 (ULift.up j) := by
    letI := modulesLinearOverField K (projection K)
    simp [LagrangianRowDifferential.rowProjection, TensorFreeRowProjection.row]
  let F := dualSheaf (LagrangianFiveSectionModel.equationBundle K)
  let P := (Scheme.Modules.pullback (p ≫ i)).obj F
  letI : Module K Γ(P,⊤) := (moduleSpecΓFunctor.obj P).isModule
  let l := (moduleSpecΓFunctor.mapIso ((Scheme.Modules.pullbackComp p i).app F)).toLinearEquiv.symm
  let T := pointLocalPullback K (p ≫ i) F U hU
  let b := fun j : Fin 5 =>
    (dualMap (TensorFreeCoordinates.projection (space K) (determinantLine K) 5 (ULift.up j))).app U τ
  calc
    _ = l (T (∑ j : Fin 5, localScalar K U (a j) • b j)) := by
      rw [localRowInput_eq_composite, rowDual_app_eq_sum]
      rfl
    _ = l (∑ j : Fin 5, a j • T (b j)) := by
      congr 1
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smulₛₗ, localScalar_point K i p hp U hU]
      rfl
    _ = ∑ j : Fin 5, a j • l (T (b j)) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => l.map_smul (a j) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      rw [localRowInput_eq_composite, hsingle]
      rfl

/-- The actual image open of the genuine translated chart. -/
abbrev translatedOpen (g : Matrix.symplecticGroup (Fin 3) K) : (space K).Opens :=
  (translatedBigCell K g).opensRange

/-- The original translated chart is genuinely isomorphic to its actual image open. -/
def translatedOpenIso (g : Matrix.symplecticGroup (Fin 3) K) :
    chart K ≅ (translatedOpen K g).toScheme :=
  IsOpenImmersion.isoOfRangeEq (translatedBigCell K g) (translatedOpen K g).ι
    (by rw [Scheme.Opens.range_ι]; rfl)

/-- The actual translated determinant frame gives an actual frame on that original open. -/
def translatedOpenFrame (g : Matrix.symplecticGroup (Fin 3) K) :
    (Scheme.Modules.pullback (translatedOpen K g).ι).obj (determinantLine K) ≅
      SheafOfModules.unit (translatedOpen K g).toScheme.ringCatSheaf := by
  let e := translatedOpenIso K g
  have h : e.inv ≫ translatedBigCell K g = (translatedOpen K g).ι :=
    IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
  exact ((Scheme.Modules.pullbackCongr h).app (determinantLine K)).symm ≪≫
    ((Scheme.Modules.pullbackComp e.inv (translatedBigCell K g)).app (determinantLine K)).symm ≪≫
      LineFramePullback.pullbackFrame e.inv
        ((Scheme.Modules.pullback (translatedBigCell K g)).obj (determinantLine K))
        (translatedDeterminantIso K g)

/-- The genuine ambient local dual functional determined by the actual chart frame. -/
def translatedLocalFunctional (g : Matrix.symplecticGroup (Fin 3) K) :
    Γ(dualSheaf (determinantLine K), translatedOpen K g) :=
  OpenPullbackFunctional.ofPullback (determinantLine K) (translatedOpen K g)
    (translatedOpenFrame K g).hom

theorem translatedLocalFunctional_pairing_one (g : Matrix.symplecticGroup (Fin 3) K) :
    ∃ m : Γ(determinantLine K, translatedOpen K g),
      evalAt (determinantLine K) (translatedLocalFunctional K g) m = 1 :=
  OpenPullbackFunctional.exists_eval_ofPullback_eq_one (determinantLine K) (translatedOpen K g)
    (translatedOpenFrame K g)

include hz in
theorem point_mem_translatedOpen :
    (p ≫ i).base (SpecFieldStalkSections.point K) ∈ translatedOpen K g := by
  change (p ≫ i).base (SpecFieldStalkSections.point K) ∈ Set.range (translatedBigCell K g)
  rw [← hz]
  exact ⟨z.base (SpecFieldStalkSections.point K), rfl⟩

/-- The actual local original dual section in the twice-pulled original line. -/
def localDualInput (U : (space K).Opens)
    (hU : (p ≫ i).base (SpecFieldStalkSections.point K) ∈ U)
    (τ : Γ(dualSheaf (determinantLine K),U)) :
    MukaiConormalRowPointFrame.PointDualLine K i p :=
  ((Scheme.Modules.pullbackComp p i).app (dualSheaf (determinantLine K))).inv.app ⊤
    (SpecFieldPullbackSections.pulledSection K (p ≫ i) (dualSheaf (determinantLine K)) U hU τ)

/-- A genuine local unit pairing survives in the actual point dual line. -/
theorem localDualInput_ne_zero (U : (space K).Opens)
    (hU : (p ≫ i).base (SpecFieldStalkSections.point K) ∈ U)
    (τ : Γ(dualSheaf (determinantLine K),U)) (m : Γ(determinantLine K,U))
    (hm : evalAt (determinantLine K) τ m = 1) : localDualInput K i p U hU τ ≠ 0 := by
  have hn := FieldPointDualPairing.pulledSection_ne_zero_of_pairing_one K (p ≫ i)
    (determinantLine K) U hU τ m hm
  let e := (moduleSpecΓFunctor.mapIso
    ((Scheme.Modules.pullbackComp p i).app (dualSheaf (determinantLine K)))).toLinearEquiv
  intro hzero
  apply hn
  apply e.symm.injective
  change localDualInput K i p U hU τ = e.symm 0
  exact hzero.trans e.symm.toLinearMap.map_zero.symm

/-- Actual native ranks give the genuine one-dimensional point dual line. -/
theorem pointDualLine_finite_and_finrank :
    Module.Finite K (MukaiConormalRowPointFrame.PointDualLine K i p) ∧
      finrank K (MukaiConormalRowPointFrame.PointDualLine K i p) = 1 := by
  let hD := LagrangianFiveSectionModel.determinantLine_isInvertible K
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (determinantLine K) 1 :=
    @SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible (space K) (determinantLine K) hD
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (dualSheaf (determinantLine K)) 1 :=
    isFiniteLocallyFreeOfRank_dualSheaf (determinantLine K) 1 inferInstance
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback i).obj (dualSheaf (determinantLine K))) 1 :=
    isFiniteLocallyFreeOfRank_pullback i (dualSheaf (determinantLine K)) 1
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback i).obj
        (dualSheaf (determinantLine K)))) 1 :=
    isFiniteLocallyFreeOfRank_pullback p
      ((Scheme.Modules.pullback i).obj (dualSheaf (determinantLine K))) 1
  exact MukaiConormalFieldCoordinates.finite_and_finrank_sections K _ 1

/-- The translated point unit and the genuine ambient local unit differ
by a derived nonzero ORIGINAL-field scalar. -/
theorem exists_translated_local_unit_ratio :
    ∃ c : K, c ≠ 0 ∧
      MukaiConormalRowPointFrame.pointDualUnit K i p g z hz =
        c • localDualInput K i p (translatedOpen K g) (point_mem_translatedOpen K i p g z hz)
          (translatedLocalFunctional K g) := by
  obtain ⟨m,hm⟩ := translatedLocalFunctional_pairing_one K g
  have hn := localDualInput_ne_zero K i p (translatedOpen K g)
    (point_mem_translatedOpen K i p g z hz) (translatedLocalFunctional K g) m hm
  obtain ⟨_,hdim⟩ := pointDualLine_finite_and_finrank K i p
  obtain ⟨c,hc⟩ := _root_.exists_smul_eq_of_finrank_eq_one hdim hn
    (MukaiConormalRowPointFrame.pointDualUnit K i p g z hz)
  refine ⟨c, ?_, hc.symm⟩
  intro hz0
  rw [hz0, zero_smul] at hc
  exact MukaiConormalRowPointFrame.pointDualUnit_ne_zero K i p g z hz hc.symm

/-- Original dual-row pullback on a genuine ambient local functional is the actual local row input. -/
theorem localRowInput_eq_pulled_row (U : (space K).Opens)
    (hU : (p ≫ i).base (SpecFieldStalkSections.point K) ∈ U)
    (τ : Γ(dualSheaf (determinantLine K),U)) (a : Fin 5 → K) :
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
      ((Scheme.Modules.pullback i).map (dualMap (LagrangianRowDifferential.rowProjection K a))))).hom
      (localDualInput K i p U hU τ) = localRowInput K i p U hU τ a := by
  rw [localRowInput_eq_composite]
  let d := dualMap (LagrangianRowDifferential.rowProjection K a)
  let t := SpecFieldPullbackSections.pulledSection K (p ≫ i) (dualSheaf (determinantLine K)) U hU τ
  have hn := congrArg (fun m => m.app ⊤ t) ((Scheme.Modules.pullbackComp p i).inv.naturality d)
  change ((Scheme.Modules.pullbackComp p i).inv.app
      (dualSheaf (LagrangianFiveSectionModel.equationBundle K))).app ⊤
        (((Scheme.Modules.pullback (p ≫ i)).map d).app ⊤ t) =
    (((Scheme.Modules.pullback p).map ((Scheme.Modules.pullback i).map d))).app ⊤
      (((Scheme.Modules.pullbackComp p i).inv.app (dualSheaf (determinantLine K))).app ⊤ t) at hn
  exact hn.symm.trans (congrArg
    (((Scheme.Modules.pullbackComp p i).inv.app
      (dualSheaf (LagrangianFiveSectionModel.equationBundle K))).app ⊤)
    (SpecFieldPullbackSections.pulledSection_naturality K (p ≫ i) d U hU τ))

/-- A zero original point conormal value forces the actual local original-row differential
to vanish in the actual pulled ambient cotangent. No chart or jet comparison is assumed. -/
theorem local_derivative_zero_of_map_zero [IsClosedImmersion i]
    (U : (space K).Opens) (hU : (p ≫ i).base (SpecFieldStalkSections.point K) ∈ U)
    (τ : Γ(dualSheaf (determinantLine K), U)) (a : Fin 5 → K)
    (ha : (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
      (LagrangianFibreConormalMap.sequenceMap K M hM i q hq))).hom
        (localRowInput K i p U hU τ a) = 0) :
    SpecFieldPullbackSections.pulledSection K (p ≫ i)
      (Scheme.Hom.relativeDifferentials (projection K)) U hU
      ((Scheme.Hom.universalRelativeDerivation (projection K)).d
        (evalAt (determinantLine K) τ
          ((determinantLine K).presheaf.map (homOfLE le_top).op
            (LagrangianHyperplaneCoordinates.determinantSection K (Matrix.vecMul a M))))) = 0 := by
  let α := LagrangianFibreConormalMap.sequenceMap K M hM i q hq
  let β := (LagrangianCurveConormal.sequence K i).f
  let Ω := Scheme.Hom.relativeDifferentials (projection K)
  let τE := (dualMap (LagrangianRowDifferential.rowProjection K a)).app U τ
  let u := (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
    (dualSheaf (LagrangianFiveSectionModel.equationBundle K))).app U τE)
  let v := (Scheme.Hom.universalRelativeDerivation (projection K)).d
    (evalAt (determinantLine K) τ
      ((determinantLine K).presheaf.map (homOfLE le_top).op
        (LagrangianHyperplaneCoordinates.determinantSection K (Matrix.vecMul a M))))
  have hzero : (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map (α ≫ β))).hom
      (localRowInput K i p U hU τ a) = 0 := by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    change (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map β)).hom
      ((moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map α)).hom
        (localRowInput K i p U hU τ a)) = 0
    rw [ha, map_zero]
  have hn := SpecFieldPullbackSections.pulledSection_naturality K p (α ≫ β) (i ⁻¹ᵁ U) hU u
  have hd : (α ≫ β).app (i ⁻¹ᵁ U) u =
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app Ω).app U v := by
    change (LagrangianFibreConormalMap.sequenceMap K M hM i q hq ≫
      (LagrangianCurveConormal.sequence K i).f).app (i ⁻¹ᵁ U) u = _
    rw [LagrangianFibreConormalMap.sequenceMap_firstArrow_unit_apply, row_evaluation_eq]
  rw [hd] at hn
  have hzero' := hn.symm.trans hzero
  have hc := Scheme.Modules.pullbackSection_comp p i Ω U (i ⁻¹ᵁ U) ⊤ le_rfl
    (SpecFieldPullbackSections.preimageTop K p (i ⁻¹ᵁ U) hU)
    (SpecFieldPullbackSections.preimageTop K (p ≫ i) U hU) v
  rw [pullbackSection_preimage] at hc
  have h := congrArg (fun t => ((Scheme.Modules.pullbackComp p i).app Ω).hom.app ⊤ t) hzero'
  exact hc.symm.trans (h.trans (map_zero _))

/-- The derived source coordinates are exactly the original row dual
on the genuine translated point unit, with the ORIGINAL K scalar action. -/
theorem pointSourceEquiv_symm_eq_original_row
    (hp : p ≫ (i ≫ projection K) = 𝟙 _) (a : Fin 5 → K) :
    (pointSourceEquiv K i p g z hz).symm a =
      (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
        ((Scheme.Modules.pullback i).map (dualMap (LagrangianRowDifferential.rowProjection K a))))).hom
        (MukaiConormalRowPointFrame.pointDualUnit K i p g z hz) := by
  classical
  let U := translatedOpen K g
  let hU := point_mem_translatedOpen K i p g z hz
  let τ := translatedLocalFunctional K g
  let σ := localDualInput K i p U hU τ
  let R := fun j : Fin 5 => (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
    ((Scheme.Modules.pullback i).map (dualMap
      (TensorFreeCoordinates.projection (space K) (determinantLine K) 5 (ULift.up j)))))).hom
  let A := (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
    ((Scheme.Modules.pullback i).map (dualMap (LagrangianRowDifferential.rowProjection K a))))).hom
  obtain ⟨c,hc,hratio⟩ := exists_translated_local_unit_ratio K i p g z hz
  change MukaiConormalRowPointFrame.pointDualUnit K i p g z hz = c • σ at hratio
  have hsingle (j : Fin 5) : LagrangianRowDifferential.rowProjection K (Pi.single j 1) =
      TensorFreeCoordinates.projection (space K) (determinantLine K) 5 (ULift.up j) := by
    letI := modulesLinearOverField K (projection K)
    simp [LagrangianRowDifferential.rowProjection, TensorFreeRowProjection.row]
  have hR (j : Fin 5) : R j σ = localRowInput K i p U hU τ (Pi.single j 1) := by
    simpa only [hsingle] using localRowInput_eq_pulled_row K i p U hU τ (Pi.single j 1)
  have hA : A σ = localRowInput K i p U hU τ a :=
    localRowInput_eq_pulled_row K i p U hU τ a
  calc
    _ = ∑ j : Fin 5, a j • R j (MukaiConormalRowPointFrame.pointDualUnit K i p g z hz) := rfl
    _ = ∑ j : Fin 5, a j • R j (c • σ) := by rw [hratio]
    _ = c • ∑ j : Fin 5, a j • R j σ := by
      simp only [map_smul, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_comm (a j) c (R j σ)
    _ = c • localRowInput K i p U hU τ a := by
      congr 1
      rw [localRowInput_eq_sum K i p hp U hU τ a]
      exact Finset.sum_congr rfl fun j _ => congrArg (fun v => a j • v) (hR j)
    _ = c • A σ := by rw [hA]
    _ = A (c • σ) := (A.map_smul c σ).symm
    _ = _ := by rw [hratio]

/-- Zero of the genuine normalized point conormal map forces the actual
native original-row differential to vanish in the genuine translated open. -/
theorem translated_local_derivative_zero [IsClosedImmersion i]
    (hp : p ≫ (i ≫ projection K) = 𝟙 _) (a : Fin 5 → K)
    (ha : pointSequenceMap K M hM i q hq p g z hz a = 0) :
    SpecFieldPullbackSections.pulledSection K (p ≫ i)
      (Scheme.Hom.relativeDifferentials (projection K)) (translatedOpen K g)
      (point_mem_translatedOpen K i p g z hz)
      ((Scheme.Hom.universalRelativeDerivation (projection K)).d
        (evalAt (determinantLine K) (translatedLocalFunctional K g)
          ((determinantLine K).presheaf.map (homOfLE le_top).op
            (LagrangianHyperplaneCoordinates.determinantSection K (Matrix.vecMul a M))))) = 0 := by
  obtain ⟨c,hc,hratio⟩ := exists_translated_local_unit_ratio K i p g z hz
  change (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
    (LagrangianFibreConormalMap.sequenceMap K M hM i q hq))).hom
    ((pointSourceEquiv K i p g z hz).symm a) = 0 at ha
  rw [pointSourceEquiv_symm_eq_original_row K i p g z hz hp a, hratio,
    map_smul, localRowInput_eq_pulled_row, map_smul] at ha
  exact local_derivative_zero_of_map_zero K i p M hM q hq
    (translatedOpen K g) (point_mem_translatedOpen K i p g z hz) (translatedLocalFunctional K g) a
    ((smul_eq_zero.mp ha).resolve_left hc)

/-- Actual framed values retain all original primitive coefficients. -/
theorem framedSection_value (g : Matrix.symplecticGroup (Fin 3) K)
    (z : Spec (.of K) ⟶ chart K) (hz : z ≫ chartProjection K = 𝟙 _)
    (c : Fin 14 → K) :
    pointValue K z (framedSection K g c) =
      valueMap K z (sectionTuple K g) ((formsCoordinates K).symm c) := by
  rw [framedSection_eq, pointValue_sum_constants K (chartProjection K) z hz]
  simp only [valueMap, LinearMap.coe_mk, AddHom.coe_mk, formsCoordinates_symm_basis,
    MukaiConormalChartJets.value, LagrangianFieldJetCoefficients.pointValue]

/-- Actual framed point derivatives retain all original primitive coefficients. -/
theorem framedSection_derivative (g : Matrix.symplecticGroup (Fin 3) K)
    (z : Spec (.of K) ⟶ chart K) (hz : z ≫ chartProjection K = 𝟙 _)
    (c : Fin 14 → K) :
    pointDerivative K (chartProjection K) z (framedSection K g c) =
      derivativeMap K z (sectionTuple K g) ((formsCoordinates K).symm c) := by
  rw [framedSection_eq, pointDerivative_sum_constants K (chartProjection K) z hz]
  simp only [derivativeMap, LinearMap.coe_mk, AddHom.coe_mk, formsCoordinates_symm_basis,
    MukaiConormalChartJets.derivative, LagrangianFieldJetCoefficients.pointDerivative]
  rfl

end M9Native.MukaiConormalRowFirstJet
