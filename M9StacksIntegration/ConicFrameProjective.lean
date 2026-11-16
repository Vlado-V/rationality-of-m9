module

public import M9StacksIntegration.ConicFrameMap
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.StandardAffineChart
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso

/-!
# A genuine projective domain for the conic-frame rational map

The source is the determinant-open in the actual standard affine chart of
native projective eight-space. The frame entry `(0,0)` is normalized to one.
The quotient morphism is the literal adjugate-congruence family, classified
by the pinned native Grassmannian, and its source is a dense open immersion
into native projective matrix space.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.ConicFrameProjective

open M9Native.ConicFrame

variable (K : Type u) [Field K]

/-- Native projective matrix space, formed by the integral Proj base change. -/
abbrev space : Scheme.{u} := projectiveSpaceOverRing 8 (.of K)
abbrev projection : space K ⟶ Spec (.of K) := (space K) ↘ Spec (.of K)

instance space_isIntegral : IsIntegral (space K) := by
  let e := (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison K 8).iso
  apply (isIntegral_iff_irreducibleSpace_and_isReduced _).2
  exact ⟨e.hom.homeomorph.irreducibleSpace_iff.mpr inferInstance,
    isReduced_of_isOpenImmersion e.hom⟩

abbrev polynomial := MvPolynomial (Fin 8) K

/-- The standard projective chart, retaining the genuine native chart morphism. -/
def chart : Spec (.of (polynomial K)) ⟶ space K :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.renameEquiv K Equiv.ulift).toRingEquiv.toRingHom) ≫
    (AffineSpace.SpecIso (ULift.{u} (Fin 8)) (.of K)).inv ≫
    projectiveSpaceOver.affineChart 8 0 (Equiv.ulift.trans (finSuccAboveEquiv 0)) (Spec (.of K))

instance chart_isOpenImmersion : IsOpenImmersion (chart K) := by
  unfold chart
  have : IsIso (CommRingCat.ofHom
      (MvPolynomial.renameEquiv K (Equiv.ulift.{u,0} (α := Fin 8))).toRingEquiv.toRingHom) :=
    (MvPolynomial.renameEquiv K Equiv.ulift).toRingEquiv.toCommRingCatIso.isIso_hom
  infer_instance

@[reassoc] theorem chart_projection :
    chart K ≫ projection K =
      Spec.map (CommRingCat.ofHom (algebraMap K (polynomial K))) := by
  unfold chart projection
  rw [Category.assoc,Category.assoc,projectiveSpaceOver.affineChart_over,
    AffineSpace.SpecIso_inv_over,← Spec.map_comp]
  congr 1
  ext x
  simp [MvPolynomial.algebraMap_eq]

/-- The actual matrix represented in the `F₀₀≠0` chart. -/
def normalizedFrame : Mat3 (polynomial K) :=
  !![1,MvPolynomial.X 0,MvPolynomial.X 1;
     MvPolynomial.X 2,MvPolynomial.X 3,MvPolynomial.X 4;
     MvPolynomial.X 5,MvPolynomial.X 6,MvPolynomial.X 7]

theorem normalizedFrame_det_ne_zero : (normalizedFrame K).det ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval ![0,0,0,1,0,0,0,1]) h
  simp [normalizedFrame,Matrix.det_fin_three] at he

/-- The determinant is inverted in the actual affine chart ring. -/
abbrev coordinateRing := Localization.Away (normalizedFrame K).det
abbrev domain : Scheme.{u} := Spec (.of (coordinateRing K))

instance coordinateRing_isDomain : IsDomain (coordinateRing K) :=
  Localization.Away.isDomain (normalizedFrame_det_ne_zero K)

def toChart : domain K ⟶ Spec (.of (polynomial K)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (polynomial K) (coordinateRing K)))

instance toChart_isOpenImmersion : IsOpenImmersion (toChart K) := by
  unfold toChart coordinateRing
  infer_instance

/-- This is an actual dense open domain in native projective eight-space. -/
def inclusion : domain K ⟶ space K := toChart K ≫ chart K

instance inclusion_isOpenImmersion : IsOpenImmersion (inclusion K) := by
  unfold inclusion
  infer_instance

theorem inclusion_dense : DenseRange (inclusion K) :=
  (inclusion K).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)

def domainProjection : domain K ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (coordinateRing K)))

@[reassoc (attr := simp)] theorem inclusion_projection :
    inclusion K ≫ projection K = domainProjection K := by
  rw [inclusion,Category.assoc,chart_projection]
  simp only [toChart,domainProjection,← Spec.map_comp,← CommRingCat.ofHom_comp,
    IsScalarTower.algebraMap_eq K (polynomial K) (coordinateRing K)]

/-- The literal normalized frame with the determinant inverted. -/
def localizedFrame : Mat3 (coordinateRing K) :=
  (normalizedFrame K).map (algebraMap (polynomial K) (coordinateRing K))

theorem localizedFrame_det_unit : IsUnit (localizedFrame K).det := by
  rw [localizedFrame,← RingHom.mapMatrix_apply,← RingHom.map_det]
  exact IsLocalization.Away.algebraMap_isUnit (normalizedFrame K).det

/-- Global sections of the actual affine domain, through the native `ΓSpec` isomorphism. -/
def universalFrame : Mat3 Γ(domain K, ⊤) :=
  (localizedFrame K).map (Scheme.ΓSpecIso (.of (coordinateRing K))).inv.hom

theorem universalFrame_det_unit : IsUnit (universalFrame K).det := by
  rw [universalFrame,← RingHom.mapMatrix_apply,← RingHom.map_det]
  exact (localizedFrame_det_unit K).map _

/-- The actual conic-frame rational-map representative into native `Gr(4,6)`. -/
def conicMap : domain K ⟶ GrassmannianCharts.space K 4 6 :=
  ConicFrame.map (domain K) K (domainProjection K)
    (universalFrame K) (universalFrame_det_unit K)

@[reassoc (attr := simp)] theorem conicMap_projection :
    conicMap K ≫ GrassmannianCharts.projection K 4 6 = domainProjection K :=
  ConicFrame.map_projection _ _ _ _ _

/-- Its classified quotient is the literal polynomial adjugate-congruence matrix. -/
theorem conicMap_class :
    (AlgebraicGeometry.Grassmannian.functorData 4 6).objEquiv (domain K)
      ((AlgebraicGeometry.Grassmannian.schemeRepresentableBy 4 6).homEquiv
        (conicMap K ≫ GrassmannianCharts.toIntegral K 4 6)) =
      ⟦ConicFrame.presentation (domain K) (universalFrame K) (universalFrame_det_unit K)⟧ := by
  rw [conicMap,ConicFrame.map_toIntegral]
  exact ConicFrame.integralMap_class _ _ _

/-- Scalars on the native generic stalk come from the actual projective structure map. -/
instance functionField_algebra : Algebra K (space K).functionField :=
  (GrassmannianCharts.structureScalarMap K (projection K)).toAlgebra

instance domainFunctionField_algebra : Algebra K (domain K).functionField :=
  (GrassmannianCharts.structureScalarMap K (domainProjection K)).toAlgebra

/-- Restriction to the actual determinant-open preserves the original scalar structure. -/
def domainFunctionFieldEquiv : (space K).functionField ≃ₐ[K] (domain K).functionField where
  __ := (GrassmannianCharts.openImmersionFunctionFieldIso (inclusion K)).commRingCatIsoToRingEquiv
  commutes' c := by
    have h := GrassmannianCharts.openImmersionFunctionFieldIso_scalar K (inclusion K) (projection K)
    rw [inclusion_projection] at h
    exact DFunLike.congr_fun h c

/-- Rationality is derived by restricting the native generic stalk to its actual affine chart. -/
def rationalFunctionFieldEquiv :
    (space K).functionField ≃ₐ[K] FractionRing (polynomial K) := by
  let e₁ := (GrassmannianCharts.openImmersionFunctionFieldIso (chart K)).commRingCatIsoToRingEquiv
  let e₂ := (FractionRing.algEquiv (polynomial K) (Spec (.of (polynomial K))).functionField).symm
  refine { __ := e₁.trans e₂.toRingEquiv, commutes' := fun c => ?_ }
  have h := GrassmannianCharts.openImmersionFunctionFieldIso_scalar K (chart K) (projection K)
  rw [chart_projection,GrassmannianCharts.affine_structureScalarMap] at h
  change e₂ (e₁ (algebraMap K (space K).functionField c)) = _
  have h₁ : e₁ (algebraMap K (space K).functionField c) =
      algebraMap (polynomial K) (Spec (.of (polynomial K))).functionField
        (algebraMap K (polynomial K) c) := DFunLike.congr_fun h c
  rw [h₁,e₂.commutes]
  exact (IsScalarTower.algebraMap_apply K (polynomial K) (FractionRing (polynomial K)) c).symm

end M9Native.ConicFrameProjective
