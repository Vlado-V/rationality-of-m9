module

public import M9StacksIntegration.GrassmannianCharts
public import M9.GraphBundleDescent
public import Mathlib.Data.Fin.Embedding
import all StacksFrontier.AlgebraicGeometry.Recovery27.Representable.Gluing
import all StacksFrontier.AlgebraicGeometry.Recovery27.GrassmannianScheme

/-!
# The actual invertible graph chart in the native Grassmannian

The native rank-eight quotient chart has kernel columns `[I;A;X;C]`.
On the actual determinant-open it is identified with the actual relative
isomorphism chart by `C = B X`, with inverse `B = C X⁻¹`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 2048

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical Matrix

universe u

namespace M9Native.GraphGrassmannianChart
open MvPolynomial AlgebraicGeometry.Grassmannian
open M9.GraphBundleDescent

/-- Quotient pivots are exactly the last eight of the twelve ambient columns. -/
def pivot : Fin 8 ↪ Fin 12 := Fin.natAddEmb 4

@[simp] theorem pivot_apply (i : Fin 8) : pivot i = Fin.natAdd 4 i :=
  Fin.natAddEmb_apply 4 i

def head : Fin 4 ↪ Fin 12 := Fin.castLEEmb (by decide)

theorem head_notMem_pivot (j : Fin 4) : head j ∉ Set.range pivot := by
  rintro ⟨i,hi⟩
  have hv := congrArg Fin.val hi
  change 4 + i.val = j.val at hv
  omega

theorem nonpivot_lt_four (j : Fin 12) (hj : j ∉ Set.range pivot) : j.val < 4 := by
  by_contra h
  apply hj
  refine ⟨⟨j.val-4,by omega⟩,?_⟩
  apply Fin.ext
  change 4 + (j.val-4) = j.val
  omega

/-- The complement of the native quotient pivots is literally the four
kernel-head columns, in their original order. -/
def headComplementEquiv : Fin 4 ≃ {j : Fin 12 // j ∉ Set.range pivot} where
  toFun j := ⟨head j,head_notMem_pivot j⟩
  invFun j := ⟨j.val.val,nonpivot_lt_four j.val j.property⟩
  left_inv _ := rfl
  right_inv j := by apply Subtype.ext; apply Fin.ext; rfl

def coordinateIndexEquiv : ChartIndex.{u} (k := 4) (n := 12) pivot ≃ (Fin 8 × Fin 4) :=
  (Equiv.ulift.trans (Equiv.prodCongr headComplementEquiv.symm (Equiv.refl (Fin 8)))).trans
    (Equiv.prodComm _ _)

def coordinateIndex (i : Fin 8) (j : Fin 4) : ChartIndex.{u} (k := 4) (n := 12) pivot :=
  coordinateIndexEquiv.symm (i,j)

@[simp] theorem coordinateIndexEquiv_coordinateIndex (i : Fin 8) (j : Fin 4) :
    coordinateIndexEquiv.{u} (coordinateIndex.{u} i j) = (i,j) :=
  coordinateIndexEquiv.{u}.apply_symm_apply (i,j)

abbrev Row := Fin 2 ⊕ (Fin 4 ⊕ Fin 2)

def rowEquiv : Row ≃ Fin 8 :=
  (Equiv.sumCongr (Equiv.refl (Fin 2)) finSumFinEquiv).trans finSumFinEquiv

def blockRows {R : Type*} (A : BaseMatrix R) (X : FiberMatrix R) (C : BaseMatrix R) :
    Matrix (Fin 8) (Fin 4) R :=
  fun i => Sum.elim A (Sum.elim X C) (rowEquiv.symm i)

@[simp] theorem blockRows_A {R : Type*} (A : BaseMatrix R) (X : FiberMatrix R) (C : BaseMatrix R)
    (i : Fin 2) (j : Fin 4) : blockRows A X C (rowEquiv (.inl i)) j = A i j := by
  simp only [blockRows,Equiv.symm_apply_apply,Sum.elim_inl]

@[simp] theorem blockRows_X {R : Type*} (A : BaseMatrix R) (X : FiberMatrix R) (C : BaseMatrix R)
    (i j : Fin 4) : blockRows A X C (rowEquiv (.inr (.inl i))) j = X i j := by
  simp only [blockRows,Equiv.symm_apply_apply,Sum.elim_inr,Sum.elim_inl]

@[simp] theorem blockRows_C {R : Type*} (A : BaseMatrix R) (X : FiberMatrix R) (C : BaseMatrix R)
    (i : Fin 2) (j : Fin 4) : blockRows A X C (rowEquiv (.inr (.inr i))) j = C i j := by
  simp only [blockRows,Equiv.symm_apply_apply,Sum.elim_inr]

variable (K : Type u) [Field K]

abbrev nativePolynomial := GrassmannianCharts.chartPolynomial K 4 12 pivot

/-- Native quotient coordinates are negatives of the displayed kernel matrix. -/
def nativeD : Matrix (Fin 8) (Fin 4) (nativePolynomial K) :=
  fun i j => -X (coordinateIndex i j)

def nativeA : BaseMatrix (nativePolynomial K) := fun i => nativeD K (rowEquiv (.inl i))
def nativeX : FiberMatrix (nativePolynomial K) := fun i => nativeD K (rowEquiv (.inr (.inl i)))
def nativeC : BaseMatrix (nativePolynomial K) := fun i => nativeD K (rowEquiv (.inr (.inr i)))
def nativeDeterminant : nativePolynomial K := (nativeX K).det
abbrev nativeOpenRing := Localization.Away (nativeDeterminant K)

/-- The literal substitution `C = B X` into the actual localized isomorphism
chart, with the native quotient-coordinate minus sign retained. -/
def nativePolynomialToGraph : nativePolynomial K →ₐ[K] IsomChartRing K :=
  aeval (fun a => -blockRows (universalBaseLocalized (K := K) 0)
    (universalFiberLocalized (K := K))
    (universalBaseLocalized (K := K) 1 * universalFiberLocalized (K := K))
      (coordinateIndexEquiv a).1 (coordinateIndexEquiv a).2)

theorem nativePolynomialToGraph_D (i : Fin 8) (j : Fin 4) :
    nativePolynomialToGraph K (nativeD K i j) =
      blockRows (universalBaseLocalized (K := K) 0) (universalFiberLocalized (K := K))
        (universalBaseLocalized (K := K) 1 * universalFiberLocalized (K := K)) i j := by
  simp [nativeD,nativePolynomialToGraph,coordinateIndex]

theorem nativePolynomialToGraph_A :
    (nativeA K).map (nativePolynomialToGraph K).toRingHom = universalBaseLocalized (K := K) 0 := by
  ext i j
  exact (nativePolynomialToGraph_D K _ _).trans (blockRows_A _ _ _ i j)

theorem nativePolynomialToGraph_X :
    (nativeX K).map (nativePolynomialToGraph K).toRingHom = universalFiberLocalized (K := K) := by
  ext i j
  exact (nativePolynomialToGraph_D K _ _).trans (blockRows_X _ _ _ i j)

theorem nativePolynomialToGraph_C :
    (nativeC K).map (nativePolynomialToGraph K).toRingHom =
      universalBaseLocalized (K := K) 1 * universalFiberLocalized (K := K) := by
  ext i j
  exact (nativePolynomialToGraph_D K _ _).trans (blockRows_C _ _ _ i j)

theorem nativePolynomialToGraph_det :
    nativePolynomialToGraph K (nativeDeterminant K) = (universalFiberLocalized (K := K)).det := by
  rw [nativeDeterminant,AlgHom.map_det]
  exact congrArg Matrix.det (nativePolynomialToGraph_X K)

theorem nativeDeterminant_ne_zero : nativeDeterminant K ≠ 0 := by
  intro h
  have hz := congrArg (nativePolynomialToGraph K) h
  rw [nativePolynomialToGraph_det,map_zero] at hz
  exact (IsUnit.ne_zero universalFiberLocalized_det_unit) hz

instance nativeOpenRing_isDomain : IsDomain (nativeOpenRing K) :=
  Localization.Away.isDomain (nativeDeterminant_ne_zero K)

/-- The actual map out of the native chart determinant localization. -/
def nativeToGraph : nativeOpenRing K →ₐ[K] IsomChartRing K :=
  IsLocalization.Away.liftAlgHom (f := nativePolynomialToGraph K) (S := nativeOpenRing K)
    (nativeDeterminant K) ((nativePolynomialToGraph_det K).symm ▸ universalFiberLocalized_det_unit)

theorem nativeToGraph_polynomial (p : nativePolynomial K) :
    nativeToGraph K (algebraMap (nativePolynomial K) (nativeOpenRing K) p) =
      nativePolynomialToGraph K p := by
  exact IsLocalization.Away.lift_eq (nativeDeterminant K)
    ((nativePolynomialToGraph_det K).symm ▸ universalFiberLocalized_det_unit) p

def localizedA : BaseMatrix (nativeOpenRing K) :=
  (nativeA K).map (algebraMap (nativePolynomial K) (nativeOpenRing K))
def localizedX : FiberMatrix (nativeOpenRing K) :=
  (nativeX K).map (algebraMap (nativePolynomial K) (nativeOpenRing K))
def localizedC : BaseMatrix (nativeOpenRing K) :=
  (nativeC K).map (algebraMap (nativePolynomial K) (nativeOpenRing K))

theorem localizedX_det_unit : IsUnit (localizedX K).det := by
  rw [localizedX,← RingHom.mapMatrix_apply,← RingHom.map_det]
  exact IsLocalization.Away.algebraMap_isUnit (nativeDeterminant K)

def localizedIsomorphism : Matrix.GeneralLinearGroup (Fin 4) (nativeOpenRing K) :=
  Matrix.GeneralLinearGroup.mk'' (localizedX K) (localizedX_det_unit K)

/-- The actual inverse matrix formula on the native determinant-open. -/
def recoveredB : BaseMatrix (nativeOpenRing K) :=
  localizedC K * (localizedIsomorphism K)⁻¹.val

theorem recoveredB_mul_X : recoveredB K * localizedX K = localizedC K := by
  change (localizedC K * (localizedIsomorphism K)⁻¹.val) * (localizedIsomorphism K).val = _
  rw [Matrix.mul_assoc,← Units.val_mul,inv_mul_cancel,Units.val_one,Matrix.mul_one]

/-- The actual algebra map into the native determinant-open reconstructs
the second base plane using `B = C X⁻¹`. -/
def graphToNative : IsomChartRing K →ₐ[K] nativeOpenRing K :=
  chartEvaluation (localizedA K) (recoveredB K) (localizedIsomorphism K)

theorem nativeToGraph_A :
    (localizedA K).map (nativeToGraph K).toRingHom = universalBaseLocalized (K := K) 0 := by
  ext i j
  exact (nativeToGraph_polynomial K _).trans (congrFun (congrFun (nativePolynomialToGraph_A K) i) j)

theorem nativeToGraph_X :
    (localizedX K).map (nativeToGraph K).toRingHom = universalFiberLocalized (K := K) := by
  ext i j
  exact (nativeToGraph_polynomial K _).trans (congrFun (congrFun (nativePolynomialToGraph_X K) i) j)

theorem nativeToGraph_C :
    (localizedC K).map (nativeToGraph K).toRingHom =
      universalBaseLocalized (K := K) 1 * universalFiberLocalized (K := K) := by
  ext i j
  exact (nativeToGraph_polynomial K _).trans (congrFun (congrFun (nativePolynomialToGraph_C K) i) j)

theorem nativeToGraph_isomorphism :
    Matrix.GeneralLinearGroup.map (nativeToGraph K).toRingHom (localizedIsomorphism K) =
      universalIsomorphism (K := K) := by
  apply Units.ext
  exact nativeToGraph_X K

theorem nativeToGraph_B :
    (recoveredB K).map (nativeToGraph K).toRingHom = universalBaseLocalized (K := K) 1 := by
  have hi : ((localizedIsomorphism K)⁻¹.val).map (nativeToGraph K).toRingHom =
      (universalIsomorphism (K := K))⁻¹.val := by
    change (Matrix.GeneralLinearGroup.map (nativeToGraph K).toRingHom
      ((localizedIsomorphism K)⁻¹)).val = _
    rw [map_inv,nativeToGraph_isomorphism]
  rw [recoveredB,Matrix.map_mul,nativeToGraph_C,hi]
  change (universalBaseLocalized (K := K) 1 * (universalIsomorphism (K := K)).val) *
    (universalIsomorphism (K := K))⁻¹.val = _
  rw [Matrix.mul_assoc,← Units.val_mul,mul_inv_cancel,Units.val_one,Matrix.mul_one]

theorem graphToNative_A :
    (universalBaseLocalized (K := K) 0).map (graphToNative K).toRingHom = localizedA K := by
  exact chartEvaluation_base (localizedA K) (recoveredB K) (localizedIsomorphism K) 0

theorem graphToNative_B :
    (universalBaseLocalized (K := K) 1).map (graphToNative K).toRingHom = recoveredB K := by
  exact chartEvaluation_base (localizedA K) (recoveredB K) (localizedIsomorphism K) 1

theorem graphToNative_X :
    (universalFiberLocalized (K := K)).map (graphToNative K).toRingHom = localizedX K := by
  exact congrArg Units.val
    (chartEvaluation_fiber (localizedA K) (recoveredB K) (localizedIsomorphism K))

theorem nativeToGraph_graphToNative :
    (nativeToGraph K).comp (graphToNative K) = AlgHom.id K (IsomChartRing K) := by
  rw [graphToNative,chartEvaluation_baseChange,nativeToGraph_A,nativeToGraph_B,nativeToGraph_isomorphism]
  apply (isomChartHomEquiv (K := K) (R := IsomChartRing K)).injective
  apply Prod.ext
  · exact chartEvaluation_base _ _ _ 0
  · apply Prod.ext
    · exact chartEvaluation_base _ _ _ 1
    · exact chartEvaluation_fiber _ _ _

theorem nativePolynomial_algHom_ext {R : Type u} [CommRing R] [Algebra K R]
    (f g : nativePolynomial K →ₐ[K] R)
    (hA : (nativeA K).map f.toRingHom = (nativeA K).map g.toRingHom)
    (hX : (nativeX K).map f.toRingHom = (nativeX K).map g.toRingHom)
    (hC : (nativeC K).map f.toRingHom = (nativeC K).map g.toRingHom) : f = g := by
  apply MvPolynomial.algHom_ext
  intro a
  obtain ⟨⟨i,j⟩,rfl⟩ := coordinateIndexEquiv.{u}.symm.surjective a
  obtain ⟨r,rfl⟩ := rowEquiv.surjective i
  rcases r with i | (i | i)
  · have hh := congrFun (congrFun hA i) j
    change f (-X (coordinateIndex (rowEquiv (.inl i)) j)) =
      g (-X (coordinateIndex (rowEquiv (.inl i)) j)) at hh
    rw [map_neg,map_neg] at hh
    exact neg_injective hh
  · have hh := congrFun (congrFun hX i) j
    change f (-X (coordinateIndex (rowEquiv (.inr (.inl i))) j)) =
      g (-X (coordinateIndex (rowEquiv (.inr (.inl i))) j)) at hh
    rw [map_neg,map_neg] at hh
    exact neg_injective hh
  · have hh := congrFun (congrFun hC i) j
    change f (-X (coordinateIndex (rowEquiv (.inr (.inr i))) j)) =
      g (-X (coordinateIndex (rowEquiv (.inr (.inr i))) j)) at hh
    rw [map_neg,map_neg] at hh
    exact neg_injective hh

theorem graphToNative_nativeToGraph :
    (graphToNative K).comp (nativeToGraph K) = AlgHom.id K (nativeOpenRing K) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (nativeDeterminant K))
  apply nativePolynomial_algHom_ext K
  · ext i j
    change graphToNative K (nativeToGraph K (algebraMap _ _ (nativeA K i j))) = _
    rw [nativeToGraph_polynomial]
    have he := congrFun (congrFun (nativePolynomialToGraph_A K) i) j
    change nativePolynomialToGraph K (nativeA K i j) = _ at he
    rw [he]
    exact congrFun (congrFun (graphToNative_A K) i) j
  · ext i j
    change graphToNative K (nativeToGraph K (algebraMap _ _ (nativeX K i j))) = _
    rw [nativeToGraph_polynomial]
    have he := congrFun (congrFun (nativePolynomialToGraph_X K) i) j
    change nativePolynomialToGraph K (nativeX K i j) = _ at he
    rw [he]
    exact congrFun (congrFun (graphToNative_X K) i) j
  · ext i j
    change graphToNative K (nativeToGraph K (algebraMap _ _ (nativeC K i j))) = _
    rw [nativeToGraph_polynomial]
    have he := congrFun (congrFun (nativePolynomialToGraph_C K) i) j
    change nativePolynomialToGraph K (nativeC K i j) = _ at he
    rw [he]
    have hm : (universalBaseLocalized (K := K) 1 * universalFiberLocalized (K := K)).map
        (graphToNative K).toRingHom = localizedC K := by
      rw [Matrix.map_mul,graphToNative_B,graphToNative_X,recoveredB_mul_X]
    exact congrFun (congrFun hm i) j

/-- Genuine coordinate-ring equivalence between the native dense chart's
determinant-open and the actual relative-isomorphism chart. -/
def nativeGraphEquiv : nativeOpenRing K ≃ₐ[K] IsomChartRing K :=
  AlgEquiv.ofAlgHom (nativeToGraph K) (graphToNative K)
    (nativeToGraph_graphToNative K) (graphToNative_nativeToGraph K)

/-- The actual relative-isomorphism chart as an affine scheme. -/
abbrev domain := Spec (.of (IsomChartRing K))

def toNativeOpen : domain K ⟶ Spec (.of (nativeOpenRing K)) :=
  Spec.map (CommRingCat.ofHom (nativeGraphEquiv K).toRingHom)

instance toNativeOpen_isOpenImmersion : IsOpenImmersion (toNativeOpen K) := by
  have : IsIso (CommRingCat.ofHom (nativeGraphEquiv K).toRingHom) :=
    (nativeGraphEquiv K).toRingEquiv.toCommRingCatIso.isIso_hom
  unfold toNativeOpen
  infer_instance

def nativeOpenInclusion : Spec (.of (nativeOpenRing K)) ⟶ Spec (.of (nativePolynomial K)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (nativePolynomial K) (nativeOpenRing K)))

instance nativeOpenInclusion_isOpenImmersion : IsOpenImmersion (nativeOpenInclusion K) := by
  unfold nativeOpenInclusion nativeOpenRing
  infer_instance

/-- A genuine morphism into the native Grassmannian; it is the actual native
quotient chart restricted by the proven coordinate-ring equivalence. -/
def graphMap : domain K ⟶ GrassmannianCharts.space K 4 12 :=
  toNativeOpen K ≫ nativeOpenInclusion K ≫ GrassmannianCharts.chartSpecMap K 4 12 pivot

instance graphMap_isOpenImmersion : IsOpenImmersion (graphMap K) := by
  unfold graphMap
  infer_instance

theorem graphMap_dense : DenseRange (graphMap K) :=
  (graphMap K).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)

theorem graphMap_eq : graphMap K =
    Spec.map (CommRingCat.ofHom (nativePolynomialToGraph K).toRingHom) ≫
      GrassmannianCharts.chartSpecMap K 4 12 pivot := by
  unfold graphMap toNativeOpen nativeOpenInclusion
  rw [← Category.assoc,← Spec.map_comp,← CommRingCat.ofHom_comp]
  have he : (nativeGraphEquiv K).toRingHom.comp
      (algebraMap (nativePolynomial K) (nativeOpenRing K)) =
      (nativePolynomialToGraph K).toRingHom := by
    apply RingHom.ext
    intro p
    exact nativeToGraph_polynomial K p
  rw [he]

def domainProjection : domain K ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (IsomChartRing K)))

@[reassoc] theorem graphMap_projection :
    graphMap K ≫ GrassmannianCharts.projection K 4 12 = domainProjection K := by
  rw [graphMap_eq,Category.assoc,GrassmannianCharts.chartSpecMap_projection,
    ← Spec.map_comp,← CommRingCat.ofHom_comp]
  congr 1
  ext c
  exact (nativePolynomialToGraph K).commutes c

/-- The function field isomorphism is induced by this actual dense native
open immersion, followed by the actual localized chart fraction field. -/
def graphFunctionFieldEquiv : (GrassmannianCharts.space K 4 12).functionField ≃ₐ[K]
    ChartFunctionField K := by
  let e₁ := (GrassmannianCharts.openImmersionFunctionFieldIso (graphMap K)).commRingCatIsoToRingEquiv
  let e₂ := (FractionRing.algEquiv (IsomChartRing K) (domain K).functionField).symm
  let e₃ := localizedChartFieldEquiv K
  refine { __ := e₁.trans (e₂.toRingEquiv.trans e₃.toRingEquiv), commutes' := fun c => ?_ }
  have h := GrassmannianCharts.openImmersionFunctionFieldIso_scalar K (graphMap K)
    (GrassmannianCharts.projection K 4 12)
  rw [graphMap_projection,domainProjection,GrassmannianCharts.affine_structureScalarMap] at h
  have h₁ : e₁ (algebraMap K (GrassmannianCharts.space K 4 12).functionField c) =
      algebraMap (IsomChartRing K) (domain K).functionField
        (algebraMap K (IsomChartRing K) c) := DFunLike.congr_fun h c
  change e₃ (e₂ (e₁ (algebraMap K (GrassmannianCharts.space K 4 12).functionField c))) = _
  rw [h₁,e₂.commutes,← IsScalarTower.algebraMap_apply K (IsomChartRing K)
    (FractionRing (IsomChartRing K)) c]
  exact e₃.commutes c

/-- The rational function obtained from an actual regular function on this
actual dense graph open, using the inverse of its genuine stalk restriction. -/
def chartFunction (p : IsomChartRing K) : (GrassmannianCharts.space K 4 12).functionField :=
  (GrassmannianCharts.openImmersionFunctionFieldIso (graphMap K)).inv
    (algebraMap (IsomChartRing K) (domain K).functionField p)

theorem graphFunctionFieldEquiv_chartFunction (p : IsomChartRing K) :
    graphFunctionFieldEquiv K (chartFunction K p) =
      algebraMap (IsomChartRing K) (ChartFunctionField K) p := by
  change localizedChartFieldEquiv K
    ((FractionRing.algEquiv (IsomChartRing K) (domain K).functionField).symm
      ((GrassmannianCharts.openImmersionFunctionFieldIso (graphMap K)).hom
        ((GrassmannianCharts.openImmersionFunctionFieldIso (graphMap K)).inv
          (algebraMap (IsomChartRing K) (domain K).functionField p)))) = _
  rw [← CommRingCat.comp_apply,Iso.inv_hom_id,CommRingCat.id_apply,
    AlgEquiv.commutes]
  exact (IsLocalization.algEquiv (nonZeroDivisors (IsomChartRing K))
    (FractionRing (IsomChartRing K)) (ChartFunctionField K)).commutes p

theorem graphFunctionFieldEquiv_base (s : Fin 2) (i : Fin 2) (j : Fin 4) :
    graphFunctionFieldEquiv K (chartFunction K (universalBaseLocalized (K := K) s i j)) =
      algebraMap (ChartRing K) (ChartFunctionField K) (universalBase K s i j) := by
  rw [graphFunctionFieldEquiv_chartFunction]
  exact chartLocalizationToField_polynomial K _

theorem graphFunctionFieldEquiv_fiber (i j : Fin 4) :
    graphFunctionFieldEquiv K (chartFunction K (universalFiberLocalized (K := K) i j)) =
      chartGenericFiber K i j := by
  rw [graphFunctionFieldEquiv_chartFunction]
  exact chartLocalizationToField_polynomial K _

section ActualKernel
variable {R : Type*} [CommRing R]

def rowFunctionsEquiv : (Fin 8 → R) ≃ₗ[R] (Fin 2 → R) × ((Fin 4 → R) × (Fin 2 → R)) :=
  (LinearEquiv.funCongrLeft R R rowEquiv).trans
    ((LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin 4 ⊕ Fin 2) R R).trans
      ((LinearEquiv.refl R (Fin 2 → R)).prodCongr
        (LinearEquiv.sumArrowLequivProdArrow (Fin 4) (Fin 2) R R)))

/-- Literal ordered coordinates on the original pair of six-dimensional
ambient modules, retaining the order 4,2,4,2 used by the native quotient. -/
def ambientCoordinates : (Ambient R × Ambient R) ≃ₗ[R] (Fin 12 → R) :=
  ((LinearEquiv.funCongrLeft R R (finSumFinEquiv : Fin 4 ⊕ Fin 8 ≃ Fin 12)).trans
    ((LinearEquiv.sumArrowLequivProdArrow (Fin 4) (Fin 8) R R).trans
      (((LinearEquiv.refl R (Fin 4 → R)).prodCongr rowFunctionsEquiv).trans
        (LinearEquiv.prodAssoc R (Fin 4 → R) (Fin 2 → R) (Ambient R)).symm))).symm

theorem ambientCoordinates_apply (v : Ambient R × Ambient R) (j : Fin 12) :
    ambientCoordinates v j = Sum.elim v.1.1
      (fun i => Sum.elim v.1.2 (Sum.elim v.2.1 v.2.2) (rowEquiv.symm i))
      (finSumFinEquiv.symm j) := rfl

@[simp] theorem ambientCoordinates_head (v : Ambient R × Ambient R) (j : Fin 4) :
    ambientCoordinates v (head j) = v.1.1 j := by
  rw [ambientCoordinates_apply]
  change Sum.elim _ _ (finSumFinEquiv.symm (Fin.castAdd 8 j)) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

@[simp] theorem ambientCoordinates_pivot (v : Ambient R × Ambient R) (r : Row) :
    ambientCoordinates v (pivot (rowEquiv r)) =
      Sum.elim v.1.2 (Sum.elim v.2.1 v.2.2) r := by
  rw [ambientCoordinates_apply]
  change Sum.elim _ _ (finSumFinEquiv.symm (Fin.natAdd 4 (rowEquiv r))) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  simp only [Sum.elim_inr,Equiv.symm_apply_apply]

/-- The literal split quotient matrix `[-D | I8]`. -/
def kernelMatrix (D : Matrix (Fin 8) (Fin 4) R) : Matrix (Fin 8) (Fin 12) R :=
  fun i j => Sum.elim (fun k => -D i k) (fun k => if i = k then 1 else 0)
    (finSumFinEquiv.symm j)

theorem kernelMatrix_mulVec (D : Matrix (Fin 8) (Fin 4) R) (v : Fin 12 → R) :
    kernelMatrix D *ᵥ v = (v ∘ pivot) - D *ᵥ (v ∘ head) := by
  ext i
  simp only [Matrix.mulVec,dotProduct,Pi.sub_apply,Function.comp_apply]
  rw [Fin.sum_univ_add (a := 4) (b := 8)]
  simp only [kernelMatrix,
    finSumFinEquiv_symm_apply_castAdd,finSumFinEquiv_symm_apply_natAdd,
    Sum.elim_inl,Sum.elim_inr,ite_mul,one_mul,zero_mul,neg_mul,Finset.sum_neg_distrib]
  have hs : (∑ j : Fin 8,if i = j then v (Fin.natAdd 4 j) else 0) = v (Fin.natAdd 4 i) := by simp
  rw [hs]
  change -(∑ j : Fin 4,D i j * v (head j)) + v (pivot i) =
    v (pivot i) - ∑ j : Fin 4,D i j * v (head j)
  rw [sub_eq_add_neg,add_comm]

theorem kernelMatrix_eq_chartMatrix (D : Matrix (Fin 8) (Fin 4) R) :
    kernelMatrix D = chartMatrix (k := 4) (n := 12) pivot
      (fun a : ChartIndex.{u} (k := 4) (n := 12) pivot =>
        -D (coordinateIndexEquiv a).1 (coordinateIndexEquiv a).2) := by
  ext i j
  obtain ⟨r,rfl⟩ := (finSumFinEquiv : Fin 4 ⊕ Fin 8 ≃ Fin 12).surjective j
  rcases r with j | j
  · calc
      kernelMatrix D i ((finSumFinEquiv : Fin 4 ⊕ Fin 8 ≃ Fin 12) (.inl j)) = -D i j := by simp only [kernelMatrix,
        finSumFinEquiv_apply_left,finSumFinEquiv_symm_apply_castAdd,Sum.elim_inl]
      _ = chartMatrix (k := 4) (n := 12) pivot _ i (head j) := by
        symm
        exact chartMatrix_apply_of_notMem (k := 4) (n := 12) pivot
          (fun a : ChartIndex.{u} (k := 4) (n := 12) pivot =>
            -D (coordinateIndexEquiv a).1 (coordinateIndexEquiv a).2)
          i (head_notMem_pivot j)
  · calc
      kernelMatrix D i ((finSumFinEquiv : Fin 4 ⊕ Fin 8 ≃ Fin 12) (.inr j)) = if i = j then 1 else 0 := by
        simp only [kernelMatrix,finSumFinEquiv_apply_right,finSumFinEquiv_symm_apply_natAdd,Sum.elim_inr]
      _ = chartMatrix (k := 4) (n := 12) pivot _ i (pivot j) :=
        (chartMatrix_apply_self (k := 4) (n := 12) pivot _ i j).symm

/-- This is an actual kernel identity on the original six-plus-six ambient
module, with the existing graph family and its original literal columns. -/
theorem kernel_eq_actualGraph (A B : BaseMatrix R) (G : Matrix.GeneralLinearGroup (Fin 4) R) :
    (Matrix.toLin' (kernelMatrix (blockRows A G.val (B*G.val)))).ker =
      (ambientCoordinates.toLinearMap.comp (graphFamilyEmbedding R A B G)).range := by
  ext v
  change kernelMatrix (blockRows A G.val (B*G.val)) *ᵥ v = 0 ↔ _
  rw [kernelMatrix_mulVec,sub_eq_zero]
  constructor
  · intro hv
    refine ⟨v ∘ head,?_⟩
    change ambientCoordinates (graphFamilyEmbedding R A B G (v ∘ head)) = v
    rw [graphFamilyEmbedding_apply]
    ext j
    obtain ⟨r,rfl⟩ := (finSumFinEquiv : Fin 4 ⊕ Fin 8 ≃ Fin 12).surjective j
    rcases r with j | j
    · exact ambientCoordinates_head _ j
    · obtain ⟨r,rfl⟩ := rowEquiv.surjective j
      change ambientCoordinates _ (pivot (rowEquiv r)) = _
      rw [ambientCoordinates_pivot]
      have he := congrFun hv (rowEquiv r)
      rw [Function.comp_apply,pivot_apply] at he
      rcases r with i | (i | i) <;>
        simpa only [blockRows,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr,
          Matrix.mulVec,dotProduct,Function.comp_apply,finSumFinEquiv_apply_right]
          using he.symm
  · rintro ⟨x,rfl⟩
    change (ambientCoordinates (graphFamilyEmbedding R A B G x)) ∘ pivot =
      blockRows A G.val (B*G.val) *ᵥ ((ambientCoordinates (graphFamilyEmbedding R A B G x)) ∘ head)
    rw [graphFamilyEmbedding_apply]
    ext i
    obtain ⟨r,rfl⟩ := rowEquiv.surjective i
    rw [Function.comp_apply,ambientCoordinates_pivot]
    have hh : (ambientCoordinates ((x,A *ᵥ x),(G.val *ᵥ x,(B*G.val) *ᵥ x))) ∘ head = x := by
      funext j
      exact ambientCoordinates_head _ j
    rw [hh]
    rcases r with i | (i | i) <;>
      simp only [blockRows,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr,Matrix.mulVec,dotProduct]

end ActualKernel

def integralChartPoint : domain K ⟶
    Spec (.of (MvPolynomial (ChartIndex.{u} (k := 4) (n := 12) pivot) (ULift.{u} ℤ))) :=
  Spec.map (CommRingCat.ofHom (nativePolynomialToGraph K).toRingHom) ≫
    (AffineSpace.SpecIso (ChartIndex.{u} (k := 4) (n := 12) pivot) (.of K)).inv ≫
      AffineSpace.toSpecMvPoly _ (Spec (.of K))

theorem integralChartPoint_coordinates (a : ChartIndex.{u} (k := 4) (n := 12) pivot) :
    AffineSpace.toSpecMvPolyIntEquiv _ (integralChartPoint K) a =
      (Scheme.ΓSpecIso (.of (IsomChartRing K))).inv (nativePolynomialToGraph K (X a)) := by
  rw [integralChartPoint,AffineSpace.toSpecMvPolyIntEquiv_comp,
    AffineSpace.toSpecMvPolyIntEquiv_comp,← AffineSpace.coord,AffineSpace.SpecIso_inv_appTop_coord]
  rw [← CommRingCat.comp_apply,← Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem graphMap_toIntegral :
    graphMap K ≫ GrassmannianCharts.toIntegral K 4 12 = integralChartPoint K ≫ chart 4 12 pivot := by
  simp only [graphMap_eq,GrassmannianCharts.chartSpecMap,Category.assoc,
    GrassmannianCharts.chartOver_toIntegral,integralChartPoint,AffineSpace.toSpecMvPoly]

def graphQuotient : Stacks.FreeSheafMatrix.F (domain K) 12 ⟶ Stacks.FreeSheafMatrix.F (domain K) 8 :=
  chartQuotientMap 4 12 pivot (integralChartPoint K)

def graphSection : Stacks.FreeSheafMatrix.F (domain K) 8 ⟶ Stacks.FreeSheafMatrix.F (domain K) 12 :=
  SheafOfModules.freeMap (fun i : ULift.{u} (Fin 8) => ULift.up (pivot i.down))

theorem graphSection_quotient : graphSection K ≫ graphQuotient K = 𝟙 _ := by
  apply (SheafOfModules.freeHomEquiv (Stacks.FreeSheafMatrix.F (domain K) 8)).injective
  funext i
  apply (Stacks.FreeSheafMatrix.F (domain K) 8).unitHomEquiv.symm.injective
  rw [SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply,
    SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
  simpa only [graphSection,graphQuotient,Category.assoc,SheafOfModules.ιFree_freeMap_assoc,
    Category.comp_id] using ιFree_comp_chartQuotientMap 4 12 pivot (integralChartPoint K) i.down

theorem graphQuotient_epi : Epi (graphQuotient K) := by
  have : Epi (graphSection K ≫ graphQuotient K) := by
    rw [graphSection_quotient]
    infer_instance
  exact epi_of_epi (graphSection K) (graphQuotient K)

def graphPresentation : QuotientPresentation (domain K) 4 12 where
  target := SheafOfModules.free (R := (domain K).ringCatSheaf) (ULift.{u} (Fin (12-4)))
  map := chartQuotientMap 4 12 pivot (integralChartPoint K)
  map_epi := graphQuotient_epi K
  finiteLocallyFree := free_isFiniteLocallyFreeOfRank (domain K) (12-4)

/-- The actual classified quotient of the genuine native Grassmannian map. -/
theorem graphMap_class :
    (functorData 4 12).objEquiv (domain K)
      ((schemeRepresentableBy 4 12).homEquiv
        (graphMap K ≫ GrassmannianCharts.toIntegral K 4 12)) =
      ⟦graphPresentation K⟧ := by
  rw [graphMap_toIntegral]
  exact private_decl% (by
    have h := objEquiv_homEquiv_comp_chartMap 4 12 pivot (integralChartPoint K)
    refine h.trans (Quotient.sound (.rel _ _ ⟨Iso.refl _,?_⟩))
    dsimp only [normalizedQuotientPresentation,graphPresentation,graphQuotient]
    simp only [chartQuotientMap,Iso.refl_hom,Category.comp_id])

theorem graphPresentation_map : (graphPresentation K).map = graphQuotient K := rfl

def globalBase (s : Fin 2) : BaseMatrix Γ(domain K,⊤) :=
  (universalBaseLocalized (K := K) s).map (Scheme.ΓSpecIso (.of (IsomChartRing K))).inv.hom

def globalIsomorphism : Matrix.GeneralLinearGroup (Fin 4) Γ(domain K,⊤) :=
  Matrix.GeneralLinearGroup.map (Scheme.ΓSpecIso (.of (IsomChartRing K))).inv.hom
    (universalIsomorphism (K := K))

theorem blockRows_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A : BaseMatrix R) (X : FiberMatrix R) (C : BaseMatrix R) :
    (blockRows A X C).map f = blockRows (A.map f) (X.map f) (C.map f) := by
  ext i j
  obtain ⟨r,rfl⟩ := rowEquiv.surjective i
  rcases r with i | (i | i) <;> simp [blockRows]

/-- The actual free-sheaf quotient matrix is literally `[-A;-X;-BX | I8]`. -/
theorem graphQuotient_matrix : Stacks.FreeSheafMatrix.toMatrix (graphQuotient K) =
    kernelMatrix (blockRows (globalBase K 0) (globalIsomorphism K).val
      (globalBase K 1 * (globalIsomorphism K).val)) := by
  rw [graphQuotient,toMatrix_chartQuotientMap,kernelMatrix_eq_chartMatrix]
  congr 1
  funext a
  rw [integralChartPoint_coordinates]
  simp only [nativePolynomialToGraph,aeval_X,map_neg]
  have hm := blockRows_map (Scheme.ΓSpecIso (.of (IsomChartRing K))).inv.hom
    (universalBaseLocalized (K := K) 0) (universalFiberLocalized (K := K))
    (universalBaseLocalized (K := K) 1 * universalFiberLocalized (K := K))
  rw [Matrix.map_mul] at hm
  exact congrArg Neg.neg (congrFun (congrFun hm (coordinateIndexEquiv a).1) (coordinateIndexEquiv a).2)

/-- The quotient classified by the native dense-open morphism has exactly
the kernel of the original actual graph-family embedding. -/
theorem graphQuotient_kernel :
    (Matrix.toLin' (Stacks.FreeSheafMatrix.toMatrix (graphQuotient K))).ker =
      (ambientCoordinates.toLinearMap.comp (graphFamilyEmbedding Γ(domain K,⊤)
        (globalBase K 0) (globalBase K 1) (globalIsomorphism K))).range := by
  rw [graphQuotient_matrix]
  exact kernel_eq_actualGraph _ _ _

instance domainFunctionField_algebra : Algebra K (domain K).functionField :=
  (GrassmannianCharts.structureScalarMap K (domainProjection K)).toAlgebra

/-- Restriction to the actual graph open as an equivalence of its genuine
native generic stalks, preserving the original structure morphism to K. -/
def grassmannianGraphStalkEquiv : (GrassmannianCharts.space K 4 12).functionField ≃ₐ[K]
    (domain K).functionField where
  __ := (GrassmannianCharts.openImmersionFunctionFieldIso (graphMap K)).commRingCatIsoToRingEquiv
  commutes' c := by
    have h := GrassmannianCharts.openImmersionFunctionFieldIso_scalar K (graphMap K)
      (GrassmannianCharts.projection K 4 12)
    rw [graphMap_projection] at h
    exact DFunLike.congr_fun h c

/-- The actual generic-stalk field of the represented relative isomorphism
chart has its original base and matrix coordinates. -/
def graphStalkCoordinates : (domain K).functionField ≃ₐ[K] ChartFunctionField K :=
  (grassmannianGraphStalkEquiv K).symm.trans (graphFunctionFieldEquiv K)

theorem graphStalkCoordinates_coordinate (p : IsomChartRing K) :
    graphStalkCoordinates K (algebraMap (IsomChartRing K) (domain K).functionField p) =
      algebraMap (IsomChartRing K) (ChartFunctionField K) p :=
  graphFunctionFieldEquiv_chartFunction K p

end M9Native.GraphGrassmannianChart
