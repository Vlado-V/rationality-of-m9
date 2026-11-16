module

public import M9StacksIntegration.GrassmannianCharts
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! Actual dense matrix charts in the native product Grassmannian. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace M9Native.GrassmannianProductCharts

open AlgebraicGeometry.Grassmannian

/-- Geometric integrality follows from the already proved native matrix
chart integrality over every field, through the actual base-change square. -/
instance integralModel_geometricallyIntegral (r n : ℕ) :
    GeometricallyIntegral (terminal.from (scheme.{u} r n)) := by
  constructor
  intro K hK y Z fst snd h
  have hy : y = terminal.from (Spec (.of K)) := terminal.hom_ext _ _
  subst y
  let e : Z ≅ GrassmannianCharts.space K r n := h.flip.isoPullback
  exact IsIntegral.of_isIso e.inv

variable (K : Type u) [Field K] (r n : ℕ)

instance projection_geometricallyIntegral :
    GeometricallyIntegral (GrassmannianCharts.projection K r n) := by
  change GeometricallyIntegral (pullback.fst _ _)
  infer_instance

instance projection_flat : Flat (GrassmannianCharts.projection K r n) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Flat)
    (GrassmannianCharts.matrixCover K r n)]
  intro i
  change Flat (GrassmannianCharts.chartOver K r n i ≫ GrassmannianCharts.projection K r n)
  rw [GrassmannianCharts.chartOver_projection]
  infer_instance

instance projection_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (GrassmannianCharts.projection K r n) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFinitePresentation)
    (GrassmannianCharts.matrixCover K r n)]
  intro i
  change LocallyOfFinitePresentation
    (GrassmannianCharts.chartOver K r n i ≫ GrassmannianCharts.projection K r n)
  rw [GrassmannianCharts.chartOver_projection]
  change LocallyOfFinitePresentation
    ((AffineSpace (ChartIndex.{u} i) (Spec (.of K))) ↘ Spec (.of K))
  have : Smooth
      ((AffineSpace (ChartIndex.{u} i) (Spec (.of K))) ↘ Spec (.of K)) :=
    (AffineSpace.smoothOfRelativeDimension (ChartIndex.{u} i) (Spec (.of K))).smooth
  infer_instance

instance space_locallyNoetherian : IsLocallyNoetherian (GrassmannianCharts.space K r n) := by
  apply (isLocallyNoetherian_iff_openCover (GrassmannianCharts.matrixCover K r n)).mpr
  intro i
  change IsLocallyNoetherian (GrassmannianCharts.chartSpace K r n i)
  exact isLocallyNoetherian_of_isOpenImmersion
    (AffineSpace.SpecIso (ChartIndex.{u} i) (.of K)).hom

/-- The literal product over the original field, rather than a stipulated rational model. -/
abbrev productSpace : Scheme.{u} :=
  pullback (GrassmannianCharts.projection K r n) (GrassmannianCharts.projection K r n)

instance productSpace_isIntegral : IsIntegral (productSpace K r n) := by
  change IsIntegral (pullback (GrassmannianCharts.projection K r n)
    (GrassmannianCharts.projection K r n))
  infer_instance

def productProjection : productSpace K r n ⟶ Spec (.of K) :=
  pullback.fst _ _ ≫ GrassmannianCharts.projection K r n

instance productField_algebra : Algebra K (productSpace K r n).functionField :=
  (GrassmannianCharts.structureScalarMap K (productProjection K r n)).toAlgebra

abbrev chartRing (ι κ : Fin (n-r) ↪ Fin n) :=
  GrassmannianCharts.chartPolynomial K r n ι ⊗[K]
    GrassmannianCharts.chartPolynomial K r n κ

instance chartRing_isDomain (ι κ : Fin (n-r) ↪ Fin n) : IsDomain (chartRing K r n ι κ) :=
  (MvPolynomial.tensorEquivSum K (ChartIndex.{u} ι) (ChartIndex.{u} κ) K).toRingEquiv.isDomain_iff.mpr
    inferInstance

def chartPairMap (ι κ : Fin (n-r) ↪ Fin n) :
    pullback
      (Spec.map (CommRingCat.ofHom (algebraMap K (GrassmannianCharts.chartPolynomial K r n ι))))
      (Spec.map (CommRingCat.ofHom (algebraMap K (GrassmannianCharts.chartPolynomial K r n κ)))) ⟶
        productSpace K r n :=
  pullback.map _ _ _ _ (GrassmannianCharts.chartSpecMap K r n ι)
    (GrassmannianCharts.chartSpecMap K r n κ) (𝟙 _)
    ((Category.comp_id _).trans (GrassmannianCharts.chartSpecMap_projection K r n ι).symm)
    ((Category.comp_id _).trans (GrassmannianCharts.chartSpecMap_projection K r n κ).symm)

instance chartPairMap_isOpenImmersion (ι κ : Fin (n-r) ↪ Fin n) :
    IsOpenImmersion (chartPairMap K r n ι κ) :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance
    (GrassmannianCharts.chartSpecMap_projection K r n ι).symm
    (GrassmannianCharts.chartSpecMap_projection K r n κ).symm

/-- The actual product of the two chosen native quotient charts, expressed
on the literal tensor coordinate ring. -/
def chartSpecMap (ι κ : Fin (n-r) ↪ Fin n) :
    Spec (.of (chartRing K r n ι κ)) ⟶ productSpace K r n :=
  (pullbackSpecIso K (GrassmannianCharts.chartPolynomial K r n ι)
    (GrassmannianCharts.chartPolynomial K r n κ)).inv ≫ chartPairMap K r n ι κ

instance chartSpecMap_isOpenImmersion (ι κ : Fin (n-r) ↪ Fin n) :
    IsOpenImmersion (chartSpecMap K r n ι κ) := by
  unfold chartSpecMap
  infer_instance

@[reassoc] theorem chartSpecMap_fst (ι κ : Fin (n-r) ↪ Fin n) :
    chartSpecMap K r n ι κ ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : GrassmannianCharts.chartPolynomial K r n ι →ₐ[K]
          chartRing K r n ι κ).toRingHom) ≫
        GrassmannianCharts.chartSpecMap K r n ι := by
  simp only [chartSpecMap, chartPairMap, Category.assoc, pullback.map, pullback.lift_fst]
  rw [← Category.assoc, pullbackSpecIso_inv_fst]
  rfl

@[reassoc] theorem chartSpecMap_snd (ι κ : Fin (n-r) ↪ Fin n) :
    chartSpecMap K r n ι κ ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : GrassmannianCharts.chartPolynomial K r n κ →ₐ[K]
          chartRing K r n ι κ).toRingHom) ≫
        GrassmannianCharts.chartSpecMap K r n κ := by
  simp only [chartSpecMap, chartPairMap, Category.assoc, pullback.map, pullback.lift_snd]
  rw [← Category.assoc, pullbackSpecIso_inv_snd]
  rfl

@[reassoc] theorem chartSpecMap_projection (ι κ : Fin (n-r) ↪ Fin n) :
    chartSpecMap K r n ι κ ≫ productProjection K r n =
      Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K r n ι κ))) := by
  rw [productProjection, ← Category.assoc, chartSpecMap_fst, Category.assoc,
    GrassmannianCharts.chartSpecMap_projection, ← Spec.map_comp]
  rfl

theorem chartSpecMap_dense (ι κ : Fin (n-r) ↪ Fin n) :
    DenseRange (chartSpecMap K r n ι κ) :=
  (chartSpecMap K r n ι κ).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)

/-- The actual native product generic stalk is compared with the fraction
field of the tensor chart by restriction along that exact dense chart. -/
def chartFunctionFieldEquiv (ι κ : Fin (n-r) ↪ Fin n) :
    (productSpace K r n).functionField ≃ₐ[K] FractionRing (chartRing K r n ι κ) := by
  let e₁ := (GrassmannianCharts.openImmersionFunctionFieldIso
    (chartSpecMap K r n ι κ)).commRingCatIsoToRingEquiv
  let e₂ := (FractionRing.algEquiv (chartRing K r n ι κ)
    (Spec (.of (chartRing K r n ι κ))).functionField).symm
  refine { __ := e₁.trans e₂.toRingEquiv, commutes' := fun c => ?_ }
  have h := GrassmannianCharts.openImmersionFunctionFieldIso_scalar K
    (chartSpecMap K r n ι κ) (productProjection K r n)
  rw [chartSpecMap_projection] at h
  change _ = GrassmannianCharts.structureScalarMap K
    (Spec.map (CommRingCat.ofHom (algebraMap K (chartRing K r n ι κ)))) at h
  rw [GrassmannianCharts.affine_structureScalarMap] at h
  have hc : e₁ (algebraMap K (productSpace K r n).functionField c) =
      algebraMap (chartRing K r n ι κ) (Spec (.of (chartRing K r n ι κ))).functionField
        (algebraMap K (chartRing K r n ι κ) c) := DFunLike.congr_fun h c
  change e₂ (e₁ (algebraMap K (productSpace K r n).functionField c)) = _
  rw [hc, e₂.commutes]
  exact (IsScalarTower.algebraMap_apply K (chartRing K r n ι κ)
    (FractionRing (chartRing K r n ι κ)) c).symm

end M9Native.GrassmannianProductCharts
