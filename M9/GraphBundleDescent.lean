module

public import M9.GraphCharts
public import M9.DeterminantTwistField
public import M9.DeterminantTwistBaseChange
public import M9.RationalExtensionAssembly
public import M9.PrimitiveRepresentation
public import Mathlib.RingTheory.Grassmannian
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Determinant

/-!
# Native graph-family charts and determinant-adjusted frame transitions

The big cell is built from actual graph submodules over arbitrary commutative
rings. Its tautological module and quotient have explicit free frames. The
relative isomorphism chart is represented by the polynomial coordinate ring
in two `2×4` base matrices and one `4×4` fiber matrix, localized at the fiber
determinant.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open scoped Classical Matrix TensorProduct

namespace M9.GraphBundleDescent

open Module LinearMap MvPolynomial

abbrev Head (R : Type*) := Fin 4 → R
abbrev Tail (R : Type*) := Fin 2 → R
abbrev Ambient (R : Type*) := Head R × Tail R
abbrev BaseMatrix (R : Type*) := Matrix (Fin 2) (Fin 4) R
abbrev FiberMatrix (R : Type*) := Matrix (Fin 4) (Fin 4) R

section BigCell
variable (R : Type*) [CommRing R]

def cell (A : BaseMatrix R) : Submodule R (Ambient R) := (Matrix.toLin' A).graph

@[simp] theorem mem_cell (A : BaseMatrix R) (v : Ambient R) :
    v ∈ cell R A ↔ v.2 = A *ᵥ v.1 := Iff.rfl

/-- The actual rank-four tautological frame over the matrix big cell. -/
def cellFrame (A : BaseMatrix R) : Head R ≃ₗ[R] cell R A where
  toFun x := ⟨(x,A *ᵥ x),rfl⟩
  invFun x := x.val.1
  left_inv _ := rfl
  right_inv x := Subtype.ext (Prod.ext rfl x.property.symm)
  map_add' x y := Subtype.ext (by simp [Matrix.mulVec_add])
  map_smul' a x := Subtype.ext (by simp [Matrix.mulVec_smul])

@[simp] theorem cellFrame_val (A : BaseMatrix R) (x : Head R) :
    (cellFrame R A x).val = (x,A *ᵥ x) := rfl

def headRestriction (U : Submodule R (Ambient R)) : U →ₗ[R] Head R :=
  (LinearMap.fst R _ _).comp U.subtype

def BigCell := {U : Submodule R (Ambient R) // Function.Bijective (headRestriction R U)}

def bigCellOfMatrix (A : BaseMatrix R) : BigCell R :=
  ⟨cell R A, by
    change Function.Bijective (fun x : cell R A => x.val.1)
    exact (cellFrame R A).symm.bijective⟩

def bigCellFrame (U : BigCell R) : Head R ≃ₗ[R] U.val :=
  (LinearEquiv.ofBijective (headRestriction R U.val) U.property).symm

def bigCellMatrix (U : BigCell R) : BaseMatrix R :=
  LinearMap.toMatrix' ((LinearMap.snd R _ _).comp (U.val.subtype.comp (bigCellFrame R U).toLinearMap))

theorem bigCellFrame_val (U : BigCell R) (x : Head R) :
    (bigCellFrame R U x).val = (x,bigCellMatrix R U *ᵥ x) := by
  apply Prod.ext
  · exact LinearEquiv.apply_symm_apply (LinearEquiv.ofBijective (headRestriction R U.val) U.property) x
  · rw [bigCellMatrix, LinearMap.toMatrix'_mulVec]
    rfl

theorem cell_bigCellMatrix (U : BigCell R) : cell R (bigCellMatrix R U) = U.val := by
  ext v
  constructor
  · intro hv
    have hframe := bigCellFrame_val R U v.1
    have heq : (bigCellFrame R U v.1).val = v := by
      rw [hframe]
      exact Prod.ext rfl hv.symm
    exact heq ▸ (bigCellFrame R U v.1).property
  · intro hv
    let x : U.val := ⟨v,hv⟩
    have heq := bigCellFrame_val R U ((bigCellFrame R U).symm x)
    rw [LinearEquiv.apply_symm_apply] at heq
    exact (congrArg Prod.snd heq).trans
      (congrArg (fun h => bigCellMatrix R U *ᵥ h) (congrArg Prod.fst heq).symm)

theorem cell_injective : Function.Injective (cell R) := by
  intro A B h
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  have hx : (x,A *ᵥ x) ∈ cell R B := h ▸ (cellFrame R A x).property
  exact hx

def bigCellEquiv : BigCell R ≃ BaseMatrix R where
  toFun := bigCellMatrix R
  invFun := bigCellOfMatrix R
  left_inv U := Subtype.ext (cell_bigCellMatrix R U)
  right_inv A := cell_injective R (cell_bigCellMatrix R (bigCellOfMatrix R A))

/-- The complementary quotient map is polynomial in the base matrix. -/
def cellQuotientMap (A : BaseMatrix R) : Ambient R →ₗ[R] Tail R :=
  (-(Matrix.toLin' A)).coprod LinearMap.id

theorem cell_ker (A : BaseMatrix R) : cell R A = (cellQuotientMap R A).ker :=
  LinearMap.graph_eq_ker_coprod _

theorem cellQuotientMap_surjective (A : BaseMatrix R) : Function.Surjective (cellQuotientMap R A) := by
  intro y
  exact ⟨(0,y),by simp [cellQuotientMap]⟩

def cellQuotientEquiv (A : BaseMatrix R) : (Ambient R ⧸ cell R A) ≃ₗ[R] Tail R :=
  (Submodule.quotEquivOfEq _ _ (cell_ker R A)).trans
    ((cellQuotientMap R A).quotKerEquivOfSurjective (cellQuotientMap_surjective R A))

variable [Nontrivial R]

/-- A point of Mathlib's native quotient-rank-two Grassmannian, hence the
subspace-rank-four convention used for `Gr(4,6)` in the manuscript. -/
def grassmannPoint (A : BaseMatrix R) : Module.Grassmannian R (Ambient R) 2 where
  toSubmodule := cell R A
  finite_quotient := Module.Finite.equiv (cellQuotientEquiv R A).symm
  projective_quotient := Module.Projective.of_equiv (cellQuotientEquiv R A).symm
  rankAtStalk_eq p := by
    rw [Module.rankAtStalk_eq_of_equiv (cellQuotientEquiv R A)]
    simp [Tail, Module.finrank_fintype_fun_eq_card]

theorem cell_rank_four (A : BaseMatrix R) : finrank R (cell R A) = 4 := by
  rw [← (cellFrame R A).finrank_eq]
  simp [Head]

end BigCell

section Fiber
variable (R : Type*) [CommRing R]

def matrixLinearEquiv : Matrix.GeneralLinearGroup (Fin 4) R ≃* (Head R ≃ₗ[R] Head R) :=
  Matrix.GeneralLinearGroup.toLin.trans (LinearMap.GeneralLinearGroup.generalLinearEquiv R (Head R))

def isomFromMatrix (A B : BaseMatrix R) (X : Matrix.GeneralLinearGroup (Fin 4) R) :
    cell R A ≃ₗ[R] cell R B :=
  (cellFrame R A).symm.trans ((matrixLinearEquiv R X).trans (cellFrame R B))

theorem isomFromMatrix_frame (A B : BaseMatrix R) (X : Matrix.GeneralLinearGroup (Fin 4) R)
    (x : Head R) :
    isomFromMatrix R A B X (cellFrame R A x) = cellFrame R B ((X : FiberMatrix R) *ᵥ x) := by
  simp only [isomFromMatrix, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

/-- The actual graph family has literal column blocks `[I; A; X; BX]`. -/
def graphFamilyEmbedding (A B : BaseMatrix R) (X : Matrix.GeneralLinearGroup (Fin 4) R) :
    Head R →ₗ[R] (Ambient R × Ambient R) :=
  (((cell R A).subtype).comp (cellFrame R A).toLinearMap).prod
    (((cell R B).subtype).comp
      (((cellFrame R B).toLinearMap).comp (matrixLinearEquiv R X).toLinearMap))

theorem graphFamilyEmbedding_apply (A B : BaseMatrix R) (X : Matrix.GeneralLinearGroup (Fin 4) R)
    (x : Head R) : graphFamilyEmbedding R A B X x =
      ((x,A *ᵥ x), ((X : FiberMatrix R) *ᵥ x, (B * (X : FiberMatrix R)) *ᵥ x)) := by
  change ((x,A *ᵥ x), ((X : FiberMatrix R) *ᵥ x, B *ᵥ ((X : FiberMatrix R) *ᵥ x))) = _
  rw [Matrix.mulVec_mulVec]

theorem graphFamilyEmbedding_injective (A B : BaseMatrix R) (X : Matrix.GeneralLinearGroup (Fin 4) R) :
    Function.Injective (graphFamilyEmbedding R A B X) := by
  intro x y h
  exact congrArg (fun v : Ambient R × Ambient R => v.1.1) h

def isomCoordinates (A B : BaseMatrix R) :
    (cell R A ≃ₗ[R] cell R B) ≃ Matrix.GeneralLinearGroup (Fin 4) R where
  toFun f := (matrixLinearEquiv R).symm ((cellFrame R A).trans (f.trans (cellFrame R B).symm))
  invFun := isomFromMatrix R A B
  left_inv f := by
    apply LinearEquiv.ext
    intro x
    simp [isomFromMatrix, LinearEquiv.trans_apply]
  right_inv X := by
    apply (matrixLinearEquiv R).injective
    simp only [MulEquiv.apply_symm_apply]
    apply LinearEquiv.ext
    intro x
    simp [isomFromMatrix, LinearEquiv.trans_apply]

end Fiber

abbrev BaseIndex := Fin 2 × (Fin 2 × Fin 4)
abbrev FiberIndex := Fin 4 × Fin 4
abbrev ParameterIndex := BaseIndex ⊕ FiberIndex

section UniversalFamily
variable (K : Type*) [Field K]

abbrev ChartRing := MvPolynomial ParameterIndex K

def universalBase (s : Fin 2) : BaseMatrix (ChartRing K) :=
  fun i j => X (Sum.inl (s,(i,j)))

def universalFiber : FiberMatrix (ChartRing K) := fun i j => X (Sum.inr (i,j))
def universalDeterminant : ChartRing K := (universalFiber K).det
abbrev IsomChartRing := Localization.Away (universalDeterminant K)

variable {K} {R : Type*} [CommRing R] [Algebra K R]

/-- Evaluation on all base and fiber coordinates is the actual polynomial
universal property, before inverting the fiber determinant. -/
def chartPolynomialMap (A B : BaseMatrix R) (G : Matrix.GeneralLinearGroup (Fin 4) R) :
    ChartRing K →ₐ[K] R :=
  aeval (Sum.elim (fun p : BaseIndex => ![A,B] p.1 p.2.1 p.2.2)
    (fun p : FiberIndex => G.val p.1 p.2))

theorem chartPolynomialMap_base_zero (A B : BaseMatrix R) (G : Matrix.GeneralLinearGroup (Fin 4) R)
    (i : Fin 2) (j : Fin 4) :
    chartPolynomialMap A B G (universalBase K 0 i j) = A i j := by
  simp [chartPolynomialMap, universalBase]

theorem chartPolynomialMap_base_one (A B : BaseMatrix R) (G : Matrix.GeneralLinearGroup (Fin 4) R)
    (i : Fin 2) (j : Fin 4) :
    chartPolynomialMap A B G (universalBase K 1 i j) = B i j := by
  simp [chartPolynomialMap, universalBase]

theorem chartPolynomialMap_fiber (A B : BaseMatrix R) (G : Matrix.GeneralLinearGroup (Fin 4) R)
    (i j : Fin 4) : chartPolynomialMap A B G (universalFiber K i j) = G.val i j := by
  simp [chartPolynomialMap, universalFiber]

theorem chartPolynomialMap_det (A B : BaseMatrix R) (G : Matrix.GeneralLinearGroup (Fin 4) R) :
    chartPolynomialMap A B G (universalDeterminant K) = G.val.det := by
  rw [universalDeterminant, AlgHom.map_det]
  congr 1
  ext i j
  exact chartPolynomialMap_fiber A B G i j

theorem universalDeterminant_ne_zero : universalDeterminant K ≠ 0 := by
  intro h
  have hm := chartPolynomialMap_det (K := K) (0 : BaseMatrix K) 0 1
  rw [h, map_zero, Units.val_one, Matrix.det_one] at hm
  exact zero_ne_one hm

/-- The universal relative-isomorphism chart over the product of Grassmann
big cells is represented by a genuine localization of a polynomial ring. -/
def chartEvaluation (A B : BaseMatrix R) (G : Matrix.GeneralLinearGroup (Fin 4) R) :
    IsomChartRing K →ₐ[K] R :=
  IsLocalization.Away.liftAlgHom (universalDeterminant K)
    (show IsUnit (chartPolynomialMap (K := K) A B G (universalDeterminant K)) from
      (chartPolynomialMap_det (K := K) A B G).symm ▸ Matrix.isUnits_det_units G)

theorem chartEvaluation_polynomial (A B : BaseMatrix R) (G : Matrix.GeneralLinearGroup (Fin 4) R)
    (P : ChartRing K) :
    chartEvaluation A B G (algebraMap (ChartRing K) (IsomChartRing K) P) = chartPolynomialMap A B G P := by
  exact IsLocalization.Away.lift_eq (universalDeterminant K)
    (show IsUnit (chartPolynomialMap (K := K) A B G (universalDeterminant K)) from
      (chartPolynomialMap_det (K := K) A B G).symm ▸ Matrix.isUnits_det_units G) P

def universalBaseLocalized (s : Fin 2) : BaseMatrix (IsomChartRing K) :=
  (universalBase K s).map (algebraMap (ChartRing K) (IsomChartRing K))

def universalFiberLocalized : FiberMatrix (IsomChartRing K) :=
  (universalFiber K).map (algebraMap (ChartRing K) (IsomChartRing K))

theorem universalFiberLocalized_det_unit : IsUnit (universalFiberLocalized (K := K)).det := by
  have hm := (algebraMap (ChartRing K) (IsomChartRing K)).map_det (universalFiber K)
  change algebraMap (ChartRing K) (IsomChartRing K) (universalDeterminant K) =
    (universalFiberLocalized (K := K)).det at hm
  rw [← hm]
  exact IsLocalization.Away.algebraMap_isUnit _

def universalIsomorphism : Matrix.GeneralLinearGroup (Fin 4) (IsomChartRing K) :=
  Matrix.GeneralLinearGroup.mk'' (universalFiberLocalized (K := K)) universalFiberLocalized_det_unit

def evaluatedFiber (f : IsomChartRing K →ₐ[K] R) : Matrix.GeneralLinearGroup (Fin 4) R :=
  Matrix.GeneralLinearGroup.mk'' (f.mapMatrix (universalFiberLocalized (K := K)))
    (by
      rw [← AlgHom.map_det]
      exact IsUnit.map f.toRingHom universalFiberLocalized_det_unit)

theorem chartEvaluation_base (A B : BaseMatrix R) (G : Matrix.GeneralLinearGroup (Fin 4) R) (s : Fin 2) :
    (universalBaseLocalized (K := K) s).map (chartEvaluation (K := K) A B G).toRingHom = ![A,B] s := by
  ext i j
  change chartEvaluation A B G (algebraMap (ChartRing K) (IsomChartRing K)
    (universalBase K s i j)) = _
  rw [chartEvaluation_polynomial]
  fin_cases s
  · exact chartPolynomialMap_base_zero A B G i j
  · exact chartPolynomialMap_base_one A B G i j

theorem chartEvaluation_fiber (A B : BaseMatrix R) (G : Matrix.GeneralLinearGroup (Fin 4) R) :
    evaluatedFiber (chartEvaluation (K := K) A B G) = G := by
  apply Units.ext
  ext i j
  change chartEvaluation A B G (algebraMap (ChartRing K) (IsomChartRing K)
    (universalFiber K i j)) = _
  rw [chartEvaluation_polynomial]
  exact chartPolynomialMap_fiber A B G i j

/-- A classification of algebra homomorphisms from the localized coordinate
ring, with no function-field or bundle equivalence assumed as input. -/
def isomChartHomEquiv : (IsomChartRing K →ₐ[K] R) ≃
    (BaseMatrix R × BaseMatrix R × Matrix.GeneralLinearGroup (Fin 4) R) where
  toFun f := ((universalBaseLocalized (K := K) 0).map f.toRingHom,
    (universalBaseLocalized (K := K) 1).map f.toRingHom, evaluatedFiber f)
  invFun p := chartEvaluation p.1 p.2.1 p.2.2
  left_inv f := by
    let A := (universalBaseLocalized (K := K) 0).map f.toRingHom
    let B := (universalBaseLocalized (K := K) 1).map f.toRingHom
    let G := evaluatedFiber f
    change chartEvaluation (K := K) A B G = f
    apply IsLocalization.algHom_ext (Submonoid.powers (universalDeterminant K))
    ext p : 1
    change chartEvaluation (K := K) A B G
      (algebraMap (ChartRing K) (IsomChartRing K) (X p)) =
        f (algebraMap (ChartRing K) (IsomChartRing K) (X p))
    rw [chartEvaluation_polynomial]
    rcases p with ⟨s,ij⟩ | ij
    · fin_cases s
      · exact chartPolynomialMap_base_zero (K := K) A B G ij.1 ij.2
      · exact chartPolynomialMap_base_one (K := K) A B G ij.1 ij.2
    · exact chartPolynomialMap_fiber (K := K) A B G ij.1 ij.2
  right_inv p := by
    rcases p with ⟨A,B,G⟩
    exact Prod.ext (chartEvaluation_base A B G 0)
      (Prod.ext (chartEvaluation_base A B G 1) (chartEvaluation_fiber A B G))

theorem chartEvaluation_baseChange {S : Type*} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (A B : BaseMatrix R) (G : Matrix.GeneralLinearGroup (Fin 4) R) :
    f.comp (chartEvaluation A B G) = chartEvaluation (A.map f.toRingHom) (B.map f.toRingHom)
      (Matrix.GeneralLinearGroup.map f.toRingHom G) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (universalDeterminant K))
  ext p : 1
  change f (chartEvaluation A B G (algebraMap _ _ (X p))) =
    chartEvaluation (A.map f.toRingHom) (B.map f.toRingHom)
      (Matrix.GeneralLinearGroup.map f.toRingHom G) (algebraMap _ _ (X p))
  rw [chartEvaluation_polynomial, chartEvaluation_polynomial]
  rcases p with ⟨s,ij⟩ | ij
  · fin_cases s
    · simp [chartPolynomialMap]
    · simp [chartPolynomialMap]
  · simp [chartPolynomialMap]

end UniversalFamily

section NativeGrassmannianFamily
variable (K : Type*) [Field K] (R : Type*) [CommRing R] [Algebra K R]

/-- Canonical scalar extension of the actual six-dimensional ambient module. -/
def tensorAmbientCoordinates : (R ⊗[K] Ambient K) ≃ₗ[R] Ambient R :=
  (TensorProduct.prodRight K R R (Head K) (Tail K)).trans
    ((TensorProduct.piScalarRight K R R (Fin 4)).prodCongr
      (TensorProduct.piScalarRight K R R (Fin 2)))

def tensorCellQuotientMap (A : BaseMatrix R) : (R ⊗[K] Ambient K) →ₗ[R] Tail R :=
  (cellQuotientMap R A).comp (tensorAmbientCoordinates K R).toLinearMap

theorem tensorCellQuotientMap_surjective (A : BaseMatrix R) :
    Function.Surjective (tensorCellQuotientMap K R A) :=
  (cellQuotientMap_surjective R A).comp (tensorAmbientCoordinates K R).surjective

theorem tensorCell_ker (A : BaseMatrix R) :
    (tensorCellQuotientMap K R A).ker =
      (cell R A).comap (tensorAmbientCoordinates K R).toLinearMap := by
  rw [tensorCellQuotientMap, LinearMap.ker_comp, ← cell_ker]

def tensorCellQuotientEquiv (A : BaseMatrix R) :
    ((R ⊗[K] Ambient K) ⧸ (tensorCellQuotientMap K R A).ker) ≃ₗ[R] Tail R :=
  (tensorCellQuotientMap K R A).quotKerEquivOfSurjective
    (tensorCellQuotientMap_surjective K R A)

variable [Nontrivial R]

/-- This is a point of the native Grassmannian functor on the actual scalar
extension `R ⊗[K] K⁶`, rather than only a subspace over a coefficient field. -/
def tensorGrassmannPoint (A : BaseMatrix R) : Module.Grassmannian R (R ⊗[K] Ambient K) 2 where
  toSubmodule := (tensorCellQuotientMap K R A).ker
  finite_quotient := Module.Finite.equiv (tensorCellQuotientEquiv K R A).symm
  projective_quotient := Module.Projective.of_equiv (tensorCellQuotientEquiv K R A).symm
  rankAtStalk_eq p := by
    rw [Module.rankAtStalk_eq_of_equiv (tensorCellQuotientEquiv K R A)]
    simp [Tail, Module.finrank_fintype_fun_eq_card]

end NativeGrassmannianFamily

section ChartFunctionFields
variable (K : Type*) [Field K]
attribute [local instance] MvPolynomial.algebraMvPolynomial

instance isomChartRing_isDomain : IsDomain (IsomChartRing K) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (IsomChartRing K)
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr (universalDeterminant_ne_zero (K := K))))

def universalLeftGrassmannian : Module.Grassmannian (IsomChartRing K) (Ambient (IsomChartRing K)) 2 :=
  grassmannPoint (IsomChartRing K) (universalBaseLocalized (K := K) 0)

def universalRightGrassmannian : Module.Grassmannian (IsomChartRing K) (Ambient (IsomChartRing K)) 2 :=
  grassmannPoint (IsomChartRing K) (universalBaseLocalized (K := K) 1)

def universalNativeGrassmannian (s : Fin 2) :
    Module.Grassmannian (IsomChartRing K) ((IsomChartRing K) ⊗[K] Ambient K) 2 :=
  tensorGrassmannPoint K (IsomChartRing K) (universalBaseLocalized (K := K) s)

def universalTautologicalIsomorphism :
    cell (IsomChartRing K) (universalBaseLocalized (K := K) 0) ≃ₗ[IsomChartRing K]
      cell (IsomChartRing K) (universalBaseLocalized (K := K) 1) :=
  isomFromMatrix (IsomChartRing K) _ _ universalIsomorphism

def universalGraphSubmodule : Submodule (IsomChartRing K)
    (Ambient (IsomChartRing K) × Ambient (IsomChartRing K)) :=
  LinearMap.range (graphFamilyEmbedding (IsomChartRing K)
    (universalBaseLocalized (K := K) 0) (universalBaseLocalized (K := K) 1) universalIsomorphism)

abbrev ChartFunctionField := FractionRing (ChartRing K)
abbrev BaseFunctionField := FractionRing (MvPolynomial BaseIndex K)
abbrev RelativeFunctionField := FractionRing (MvPolynomial FiberIndex (BaseFunctionField K))

def chartGenericFiber : FiberMatrix (ChartFunctionField K) :=
  (universalFiber K).map (algebraMap (ChartRing K) (ChartFunctionField K))

def chartLocalizationToField : IsomChartRing K →ₐ[K] ChartFunctionField K :=
  IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom K (ChartRing K) (ChartFunctionField K))
    (S := IsomChartRing K) (universalDeterminant K)
    (show IsUnit (algebraMap (ChartRing K) (ChartFunctionField K) (universalDeterminant K)) from
      isUnit_iff_ne_zero.mpr (by
        simpa only [map_zero] using (IsFractionRing.injective (ChartRing K) (ChartFunctionField K)).ne
          (universalDeterminant_ne_zero (K := K))))

theorem chartLocalizationToField_polynomial (P : ChartRing K) :
    chartLocalizationToField K (algebraMap (ChartRing K) (IsomChartRing K) P) =
      algebraMap (ChartRing K) (ChartFunctionField K) P := by
  exact IsLocalization.Away.lift_eq (g := algebraMap (ChartRing K) (ChartFunctionField K))
    (S := IsomChartRing K) (universalDeterminant K)
      (isUnit_iff_ne_zero.mpr (by
        simpa only [map_zero] using (IsFractionRing.injective (ChartRing K) (ChartFunctionField K)).ne
          (universalDeterminant_ne_zero (K := K)))) P

instance chartLocalizationFieldAlgebra : Algebra (IsomChartRing K) (ChartFunctionField K) :=
  (chartLocalizationToField K).toRingHom.toAlgebra

instance chartLocalizationFieldTower :
    IsScalarTower (ChartRing K) (IsomChartRing K) (ChartFunctionField K) :=
  IsScalarTower.of_algebraMap_eq fun P => by
    change algebraMap (ChartRing K) (ChartFunctionField K) P =
      chartLocalizationToField K (algebraMap (ChartRing K) (IsomChartRing K) P)
    exact (chartLocalizationToField_polynomial K P).symm

instance chartLocalizationBaseFieldTower : IsScalarTower K (IsomChartRing K) (ChartFunctionField K) :=
  IsScalarTower.of_algebraMap_eq fun a => (chartLocalizationToField K).commutes a |>.symm

instance chartField_isFractionRing : IsFractionRing (IsomChartRing K) (ChartFunctionField K) :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (universalDeterminant K)) (IsomChartRing K) (ChartFunctionField K)

/-- Inverting the actual universal fiber determinant does not change the
function field of the explicitly represented relative isomorphism chart. -/
def localizedChartFieldEquiv : FractionRing (IsomChartRing K) ≃ₐ[K] ChartFunctionField K :=
  (IsLocalization.algEquiv (nonZeroDivisors (IsomChartRing K))
    (FractionRing (IsomChartRing K)) (ChartFunctionField K)).restrictScalars K

def parameterIndexEquiv : ParameterIndex ≃ Fin 32 :=
  (Fintype.equivFin ParameterIndex).trans (finCongr (by decide))

def chartFieldCoordinates32 : ChartFunctionField K ≃ₐ[K] M9.RationalField K 32 :=
  IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv K parameterIndexEquiv)

def localizedChartRationalEquiv : FractionRing (IsomChartRing K) ≃ₐ[K] M9.RationalField K 32 :=
  (localizedChartFieldEquiv K).trans (chartFieldCoordinates32 K)

/-- The actual coordinate field splits into the sixteen independent base
parameters and sixteen independent relative-Hom parameters. -/
def chartRelativeEquiv : ChartFunctionField K ≃ₐ[K] RelativeFunctionField K :=
  ((M9.rationalFieldSumVariables K BaseIndex FiberIndex).trans
    (M9.rationalFieldReindex K (Equiv.sumComm FiberIndex BaseIndex))).symm

theorem chartRelativeEquiv_fiber_coordinate (ij : FiberIndex) :
    chartRelativeEquiv K (algebraMap (ChartRing K) (ChartFunctionField K) (X (Sum.inr ij))) =
      algebraMap (MvPolynomial FiberIndex (BaseFunctionField K)) (RelativeFunctionField K) (X ij) := by
  apply (chartRelativeEquiv K).symm.injective
  rw [AlgEquiv.symm_apply_apply]
  symm
  have h := congrArg (M9.rationalFieldReindex K (Equiv.sumComm FiberIndex BaseIndex))
    (M9.rationalFieldSumVariables_algebraMap K BaseIndex FiberIndex
      (X ij : MvPolynomial FiberIndex (MvPolynomial BaseIndex K)))
  have hx : algebraMap (MvPolynomial FiberIndex (MvPolynomial BaseIndex K)) (RelativeFunctionField K) (X ij) =
      algebraMap (MvPolynomial FiberIndex (BaseFunctionField K)) (RelativeFunctionField K) (X ij) := by
    rw [IsScalarTower.algebraMap_apply (MvPolynomial FiberIndex (MvPolynomial BaseIndex K))
      (MvPolynomial FiberIndex (BaseFunctionField K)) (RelativeFunctionField K)]
    congr 1
    exact map_X _ _
  rw [hx] at h
  simpa only [chartRelativeEquiv, AlgEquiv.symm_symm, AlgEquiv.trans_apply,
    M9.rationalFieldReindex_algebraMap, sumAlgEquiv_symm_X, rename_X,
    Equiv.sumComm_apply, Sum.swap_inl] using h

theorem chartRelativeEquiv_base_coordinate (b : BaseIndex) :
    chartRelativeEquiv K (algebraMap (ChartRing K) (ChartFunctionField K) (X (Sum.inl b))) =
      algebraMap (BaseFunctionField K) (RelativeFunctionField K)
        (algebraMap (MvPolynomial BaseIndex K) (BaseFunctionField K) (X b)) := by
  apply (chartRelativeEquiv K).symm.injective
  rw [AlgEquiv.symm_apply_apply]
  symm
  have h := congrArg (M9.rationalFieldReindex K (Equiv.sumComm FiberIndex BaseIndex))
    (M9.rationalFieldSumVariables_algebraMap K BaseIndex FiberIndex
      (C (X b) : MvPolynomial FiberIndex (MvPolynomial BaseIndex K)))
  have hx : algebraMap (MvPolynomial FiberIndex (MvPolynomial BaseIndex K)) (RelativeFunctionField K) (C (X b)) =
      algebraMap (BaseFunctionField K) (RelativeFunctionField K)
        (algebraMap (MvPolynomial BaseIndex K) (BaseFunctionField K) (X b)) := by
    rw [IsScalarTower.algebraMap_apply (MvPolynomial FiberIndex (MvPolynomial BaseIndex K))
      (MvPolynomial FiberIndex (BaseFunctionField K)) (RelativeFunctionField K)]
    rw [IsScalarTower.algebraMap_apply (BaseFunctionField K)
      (MvPolynomial FiberIndex (BaseFunctionField K)) (RelativeFunctionField K)]
    exact congrArg (algebraMap (MvPolynomial FiberIndex (BaseFunctionField K)) (RelativeFunctionField K))
      (MvPolynomial.map_C (σ := FiberIndex)
        (algebraMap (MvPolynomial BaseIndex K) (BaseFunctionField K)) (X b))
  rw [hx] at h
  simpa only [chartRelativeEquiv, AlgEquiv.symm_symm, AlgEquiv.trans_apply,
    M9.rationalFieldReindex_algebraMap, sumAlgEquiv_symm_C_X, rename_X,
    Equiv.sumComm_apply, Sum.swap_inr] using h

theorem relative_fiber_independent :
    AlgebraicIndependent (BaseFunctionField K)
      (fun ij : FiberIndex => algebraMap (MvPolynomial FiberIndex (BaseFunctionField K))
        (RelativeFunctionField K) (X ij)) :=
  (MvPolynomial.algebraicIndependent_X FiberIndex (BaseFunctionField K)).map'
    (f := IsScalarTower.toAlgHom (BaseFunctionField K)
      (MvPolynomial FiberIndex (BaseFunctionField K)) (RelativeFunctionField K))
    (IsFractionRing.injective _ _)

end ChartFunctionFields

/-- The actual central character `ζ ↦ ζ²` has the whole scalar cube-root
group as image, over any commutative coefficient monoid. -/
def cubeRootSquareEquiv (R : Type*) [CommMonoid R] :
    rootsOfUnity 3 R ≃ rootsOfUnity 3 R where
  toFun a := a^2
  invFun a := a^2
  left_inv a := by
    change (a^2)^2 = a
    have ha : a^3 = 1 := by
      apply Subtype.ext
      exact (mem_rootsOfUnity 3 a.val).mp a.property
    rw [← pow_mul, show 2*2 = 3+1 by decide, pow_succ, ha, one_mul]
  right_inv a := by
    change (a^2)^2 = a
    have ha : a^3 = 1 := by
      apply Subtype.ext
      exact (mem_rootsOfUnity 3 a.val).mp a.property
    rw [← pow_mul, show 2*2 = 3+1 by decide, pow_succ, ha, one_mul]

section RelativeCenterQuotient

abbrev RelativeCentralFixed :=
  (DeterminantTwistBaseChange.scalarFixedField (BaseFunctionField ℂ)).restrictScalars ℂ

/-- The actual fixed field on the native relative-Isom chart, transported
through the checked base/fiber coordinate equivalence. -/
def chartCentralFixedField : IntermediateField ℂ (ChartFunctionField ℂ) :=
  RelativeCentralFixed.comap (chartRelativeEquiv ℂ).toAlgHom

def chartCentralAction (a : rootsOfUnity 3 ℂ) : ChartFunctionField ℂ ≃ₐ[ℂ] ChartFunctionField ℂ :=
  (chartRelativeEquiv ℂ).trans
    (((DeterminantTwistBaseChange.scalarAction (BaseFunctionField ℂ) a).restrictScalars ℂ).trans
      (chartRelativeEquiv ℂ).symm)

theorem chartCentralAction_relative (a : rootsOfUnity 3 ℂ) (f : ChartFunctionField ℂ) :
    chartRelativeEquiv ℂ (chartCentralAction a f) =
      DeterminantTwistBaseChange.scalarAction (BaseFunctionField ℂ) a (chartRelativeEquiv ℂ f) := by
  simp only [chartCentralAction, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    AlgEquiv.apply_symm_apply]

theorem chartCentralAction_base (a : rootsOfUnity 3 ℂ) (b : BaseIndex) :
    chartCentralAction a (algebraMap (ChartRing ℂ) (ChartFunctionField ℂ) (X (Sum.inl b))) =
      algebraMap (ChartRing ℂ) (ChartFunctionField ℂ) (X (Sum.inl b)) := by
  apply (chartRelativeEquiv ℂ).injective
  rw [chartCentralAction_relative, chartRelativeEquiv_base_coordinate]
  exact (DeterminantTwistBaseChange.scalarAction (BaseFunctionField ℂ) a).commutes _

theorem chartCentralAction_fiber (a : rootsOfUnity 3 ℂ) (ij : FiberIndex) :
    chartCentralAction a (algebraMap (ChartRing ℂ) (ChartFunctionField ℂ) (X (Sum.inr ij))) =
      algebraMap ℂ (ChartFunctionField ℂ) (a.val : ℂ) *
        algebraMap (ChartRing ℂ) (ChartFunctionField ℂ) (X (Sum.inr ij)) := by
  apply (chartRelativeEquiv ℂ).injective
  rw [chartCentralAction_relative, chartRelativeEquiv_fiber_coordinate, map_mul,
    AlgEquiv.commutes, chartRelativeEquiv_fiber_coordinate]
  change DeterminantTwistBaseChange.scale (BaseFunctionField ℂ)
    (DeterminantTwistBaseChange.rootUnit (BaseFunctionField ℂ) a)
      (DeterminantTwistBaseChange.genericMatrix (BaseFunctionField ℂ) ij.1 ij.2) = _
  rw [DeterminantTwistBaseChange.scale_generic_entry]
  congr 1

theorem mem_chartCentralFixedField_iff (f : ChartFunctionField ℂ) :
    f ∈ chartCentralFixedField ↔ ∀ a : rootsOfUnity 3 ℂ, chartCentralAction a f = f := by
  change chartRelativeEquiv ℂ f ∈ DeterminantTwistBaseChange.scalarFixedField (BaseFunctionField ℂ) ↔ _
  rw [DeterminantTwistBaseChange.mem_scalarFixedField_iff]
  constructor
  · intro h a
    apply (chartRelativeEquiv ℂ).injective
    rw [chartCentralAction_relative]
    exact h a
  · intro h a
    have he := congrArg (chartRelativeEquiv ℂ) (h a)
    rw [chartCentralAction_relative] at he
    exact he

/-- Reparametrizing by the manuscript's actual central character does not
alter the invariant field. -/
theorem mem_chartCentralFixedField_iff_centralCharacter (f : ChartFunctionField ℂ) :
    f ∈ chartCentralFixedField ↔ ∀ a : rootsOfUnity 3 ℂ, chartCentralAction (a^2) f = f := by
  rw [mem_chartCentralFixedField_iff]
  constructor
  · intro h a
    exact h (a^2)
  · intro h a
    obtain ⟨b,hb⟩ := (cubeRootSquareEquiv ℂ).surjective a
    change b^2 = a at hb
    rw [← hb]
    exact h b

def chartCentralActionHom : rootsOfUnity 3 ℂ →* (ChartFunctionField ℂ ≃ₐ[ℂ] ChartFunctionField ℂ) where
  toFun := chartCentralAction
  map_one' := by
    apply AlgEquiv.ext
    intro f
    apply (chartRelativeEquiv ℂ).injective
    rw [chartCentralAction_relative, map_one]
    rfl
  map_mul' a b := by
    apply AlgEquiv.ext
    intro f
    apply (chartRelativeEquiv ℂ).injective
    change chartRelativeEquiv ℂ (chartCentralAction (a*b) f) =
      chartRelativeEquiv ℂ (chartCentralAction a (chartCentralAction b f))
    rw [chartCentralAction_relative, chartCentralAction_relative, chartCentralAction_relative, map_mul]
    rfl

theorem chartCentralFixed_eq_nativeFixed : chartCentralFixedField =
    IntermediateField.fixedField chartCentralActionHom.range := by
  ext f
  rw [mem_chartCentralFixedField_iff, IntermediateField.mem_fixedField_iff]
  constructor
  · rintro h σ ⟨a,rfl⟩
    exact h a
  · intro h a
    exact h (chartCentralActionHom a) ⟨a,rfl⟩

def chartFixedEquivRelative : chartCentralFixedField ≃ₐ[ℂ] RelativeCentralFixed where
  toFun f := ⟨chartRelativeEquiv ℂ f, f.property⟩
  invFun f := ⟨(chartRelativeEquiv ℂ).symm f, by
    change chartRelativeEquiv ℂ ((chartRelativeEquiv ℂ).symm f.val) ∈ RelativeCentralFixed
    rw [AlgEquiv.apply_symm_apply]
    exact f.property⟩
  left_inv f := Subtype.ext (AlgEquiv.symm_apply_apply _ _)
  right_inv f := Subtype.ext (AlgEquiv.apply_symm_apply _ _)
  map_mul' f g := Subtype.ext (map_mul _ _ _)
  map_add' f g := Subtype.ext (map_add _ _ _)
  commutes' a := Subtype.ext ((chartRelativeEquiv ℂ).commutes a)

def relativeCentralQuotientEquiv : RelativeFunctionField ℂ ≃ₐ[ℂ] RelativeCentralFixed :=
  (DeterminantTwistBaseChange.quotientCoordinateEquiv (BaseFunctionField ℂ)).restrictScalars ℂ

/-- The central quotient on the actual algebraic graph-family chart. The
base coordinates are fixed and the fiber coordinates are twisted by det. -/
def chartCentralQuotientEquiv : ChartFunctionField ℂ ≃ₐ[ℂ] chartCentralFixedField :=
  (chartRelativeEquiv ℂ).trans (relativeCentralQuotientEquiv.trans chartFixedEquivRelative.symm)

theorem chartCentralQuotient_base_coordinate (b : BaseIndex) :
    (chartCentralQuotientEquiv
      (algebraMap (ChartRing ℂ) (ChartFunctionField ℂ) (X (Sum.inl b))) : ChartFunctionField ℂ) =
      algebraMap (ChartRing ℂ) (ChartFunctionField ℂ) (X (Sum.inl b)) := by
  apply (chartRelativeEquiv ℂ).injective
  change chartRelativeEquiv ℂ ((chartRelativeEquiv ℂ).symm
    ((DeterminantTwistBaseChange.quotientCoordinateEquiv (BaseFunctionField ℂ))
      (chartRelativeEquiv ℂ _) : RelativeFunctionField ℂ)) = _
  rw [AlgEquiv.apply_symm_apply, chartRelativeEquiv_base_coordinate]
  exact congrArg Subtype.val
    ((DeterminantTwistBaseChange.quotientCoordinateEquiv (BaseFunctionField ℂ)).commutes _)

theorem chartCentralQuotient_relative_fiber_coordinate (ij : FiberIndex) :
    chartRelativeEquiv ℂ (chartCentralQuotientEquiv
      (algebraMap (ChartRing ℂ) (ChartFunctionField ℂ) (X (Sum.inr ij))) : ChartFunctionField ℂ) =
      DeterminantTwistBaseChange.twistedMatrix (BaseFunctionField ℂ) ij.1 ij.2 := by
  change chartRelativeEquiv ℂ ((chartRelativeEquiv ℂ).symm
    ((DeterminantTwistBaseChange.quotientCoordinateEquiv (BaseFunctionField ℂ))
      (chartRelativeEquiv ℂ _) : RelativeFunctionField ℂ)) = _
  rw [AlgEquiv.apply_symm_apply, chartRelativeEquiv_fiber_coordinate]
  exact DeterminantTwistBaseChange.quotientCoordinateEquiv_coordinate _ ij

theorem chartCentralQuotient_fiber_coordinate (ij : FiberIndex) :
    (chartCentralQuotientEquiv
      (algebraMap (ChartRing ℂ) (ChartFunctionField ℂ) (X (Sum.inr ij))) : ChartFunctionField ℂ) =
      DeterminantTwist.twist (chartGenericFiber ℂ) ij.1 ij.2 := by
  apply (chartRelativeEquiv ℂ).injective
  rw [chartCentralQuotient_relative_fiber_coordinate]
  have hm : (chartGenericFiber ℂ).map (chartRelativeEquiv ℂ).toRingHom =
      DeterminantTwistBaseChange.genericMatrix (BaseFunctionField ℂ) := by
    ext i j
    exact chartRelativeEquiv_fiber_coordinate ℂ (i,j)
  have hd := (chartRelativeEquiv ℂ).map_det (chartGenericFiber ℂ)
  change chartRelativeEquiv ℂ (chartGenericFiber ℂ).det =
    ((chartGenericFiber ℂ).map (chartRelativeEquiv ℂ).toRingHom).det at hd
  rw [hm] at hd
  change (DeterminantTwistBaseChange.genericMatrix (BaseFunctionField ℂ)).det⁻¹ *
    DeterminantTwistBaseChange.genericMatrix (BaseFunctionField ℂ) ij.1 ij.2 =
      chartRelativeEquiv ℂ ((chartGenericFiber ℂ).det⁻¹ * chartGenericFiber ℂ ij.1 ij.2)
  rw [map_mul, map_inv₀, hd]
  congr 1
  exact (chartRelativeEquiv_fiber_coordinate ℂ ij).symm

def chartCentralFixedRationalEquiv : chartCentralFixedField ≃ₐ[ℂ] M9.RationalField ℂ 32 :=
  chartCentralQuotientEquiv.symm.trans (chartFieldCoordinates32 ℂ)

theorem chartCentralFixed_rational : M9.RationalOfDimension ℂ chartCentralFixedField 32 :=
  ⟨chartCentralFixedRationalEquiv⟩

end RelativeCenterQuotient

universe u

section ActualSymmetricFibers
variable (K : Type u) [Field K]

def upperSplitIndex : M9.Upper3 ≃ Fin 4 ⊕ Fin 2 :=
  (Fintype.equivFin M9.Upper3).trans ((finCongr (by decide)).trans finSumFinEquiv.symm)

/-- Fixed coordinate splitting of the actual symmetric ternary matrix space. -/
def symmetricSplit : M9.Symmetric3 K ≃ₗ[K] Ambient K :=
  (M9.symmetric3Coordinates K).trans
    ((LinearEquiv.funCongrLeft K K upperSplitIndex.symm).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin 4) (Fin 2) K K))

def ambientBasis : Basis (Fin 4 ⊕ Fin 2) K (Ambient K) :=
  (Pi.basisFun K _).map (LinearEquiv.sumArrowLequivProdArrow (Fin 4) (Fin 2) K K)

def dualSymmetricSplit : Module.Dual K (M9.Symmetric3 K) ≃ₗ[K] Ambient K :=
  (symmetricSplit K).dualMap.symm.trans
    ((ambientBasis K).dualBasis.equivFun.trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin 4) (Fin 2) K K))

variable {V : Type*} [AddCommGroup V] [Module K V]

def transportedCell (e : V ≃ₗ[K] Ambient K) (A : BaseMatrix K) : Submodule K V :=
  (cell K A).map e.symm.toLinearMap

def transportedCellFrame (e : V ≃ₗ[K] Ambient K) (A : BaseMatrix K) :
    Head K ≃ₗ[K] transportedCell K e A :=
  (cellFrame K A).trans (Submodule.equivMapOfInjective e.symm.toLinearMap e.symm.injective (cell K A))

theorem transportedCell_rank (e : V ≃ₗ[K] Ambient K) (A : BaseMatrix K) :
    finrank K (transportedCell K e A) = 4 := by
  rw [← (transportedCellFrame K e A).finrank_eq]
  simp [Head]

/-- The chart lies in the manuscript's actual `Q × Q∨` graph space. -/
def actualSymmetricGraphData (A B : BaseMatrix K) (X : Matrix.GeneralLinearGroup (Fin 4) K) :
    GraphCharts.GraphData K (M9.Symmetric3 K) (Module.Dual K (M9.Symmetric3 K)) where
  left := transportedCell K (symmetricSplit K) A
  right := transportedCell K (dualSymmetricSplit K) B
  equiv := (transportedCellFrame K (symmetricSplit K) A).symm.trans
    ((matrixLinearEquiv K X).trans (transportedCellFrame K (dualSymmetricSplit K) B))

theorem actualSymmetricGraph_rank (A B : BaseMatrix K) (X : Matrix.GeneralLinearGroup (Fin 4) K) :
    finrank K (GraphCharts.graph (actualSymmetricGraphData K A B X)) = 4 := by
  rw [GraphCharts.finrank_graph]
  exact transportedCell_rank K _ _

variable (R : Type u) [CommRing R] [Algebra K R]

def tensorCoordinatesOfSplit (e : V ≃ₗ[K] Ambient K) :
    (R ⊗[K] V) ≃ₗ[R] Ambient R :=
  (e.baseChange K R V (Ambient K)).trans (tensorAmbientCoordinates K R)

def tensorSplitQuotientMap (e : V ≃ₗ[K] Ambient K) (A : BaseMatrix R) :
    (R ⊗[K] V) →ₗ[R] Tail R :=
  (cellQuotientMap R A).comp (tensorCoordinatesOfSplit K R e).toLinearMap

theorem tensorSplitQuotientMap_surjective (e : V ≃ₗ[K] Ambient K) (A : BaseMatrix R) :
    Function.Surjective (tensorSplitQuotientMap K R e A) :=
  (cellQuotientMap_surjective R A).comp (tensorCoordinatesOfSplit K R e).surjective

def tensorSplitQuotientEquiv (e : V ≃ₗ[K] Ambient K) (A : BaseMatrix R) :
    ((R ⊗[K] V) ⧸ (tensorSplitQuotientMap K R e A).ker) ≃ₗ[R] Tail R :=
  (tensorSplitQuotientMap K R e A).quotKerEquivOfSurjective
    (tensorSplitQuotientMap_surjective K R e A)

def tensorTautologicalFrame (e : V ≃ₗ[K] Ambient K) (A : BaseMatrix R) :
    Head R ≃ₗ[R] (tensorSplitQuotientMap K R e A).ker where
  toFun x := ⟨(tensorCoordinatesOfSplit K R e).symm (cellFrame R A x).val, by
    change cellQuotientMap R A
      (tensorCoordinatesOfSplit K R e ((tensorCoordinatesOfSplit K R e).symm (cellFrame R A x).val)) = 0
    rw [LinearEquiv.apply_symm_apply]
    change -(A *ᵥ x) + A *ᵥ x = 0
    exact neg_add_cancel _⟩
  invFun x := (tensorCoordinatesOfSplit K R e x.val).1
  left_inv x := by simp
  right_inv x := by
    apply Subtype.ext
    apply (tensorCoordinatesOfSplit K R e).injective
    rw [LinearEquiv.apply_symm_apply]
    have hx : tensorCoordinatesOfSplit K R e x.val ∈ cell R A := by
      rw [cell_ker]
      exact x.property
    exact Prod.ext rfl hx.symm
  map_add' x y := Subtype.ext (by
    change (tensorCoordinatesOfSplit K R e).symm (x+y,A *ᵥ (x+y)) = _
    rw [Matrix.mulVec_add]
    exact (tensorCoordinatesOfSplit K R e).symm.map_add (x,A *ᵥ x) (y,A *ᵥ y))
  map_smul' a x := Subtype.ext (by
    change (tensorCoordinatesOfSplit K R e).symm (a • x,A *ᵥ (a • x)) = _
    rw [Matrix.mulVec_smul]
    exact (tensorCoordinatesOfSplit K R e).symm.map_smul a (x,A *ᵥ x))

variable [Nontrivial R]

theorem tensorTautological_rank (e : V ≃ₗ[K] Ambient K) (A : BaseMatrix R) :
    finrank R (tensorSplitQuotientMap K R e A).ker = 4 := by
  rw [← (tensorTautologicalFrame K R e A).finrank_eq]
  simp [Head]

def tensorGrassmannOfSplit (e : V ≃ₗ[K] Ambient K) (A : BaseMatrix R) :
    Module.Grassmannian R (R ⊗[K] V) 2 where
  toSubmodule := (tensorSplitQuotientMap K R e A).ker
  finite_quotient := Module.Finite.equiv (tensorSplitQuotientEquiv K R e A).symm
  projective_quotient := Module.Projective.of_equiv (tensorSplitQuotientEquiv K R e A).symm
  rankAtStalk_eq p := by
    rw [Module.rankAtStalk_eq_of_equiv (tensorSplitQuotientEquiv K R e A)]
    simp [Tail, Module.finrank_fintype_fun_eq_card]

/-- The universal source plane is an actual native Grassmannian-functor
point on the scalar extension of the actual symmetric-matrix space `Q`. -/
def universalSymmetricGrassmannianLeft :
    Module.Grassmannian (IsomChartRing K) ((IsomChartRing K) ⊗[K] (M9.Symmetric3 K)) 2 :=
  tensorGrassmannOfSplit K (IsomChartRing K) (symmetricSplit K) (universalBaseLocalized (K := K) 0)

/-- The universal target plane is on the scalar extension of the actual dual `Q∨`. -/
def universalSymmetricGrassmannianRight :
    Module.Grassmannian (IsomChartRing K)
      ((IsomChartRing K) ⊗[K] (Module.Dual K (M9.Symmetric3 K))) 2 :=
  tensorGrassmannOfSplit K (IsomChartRing K) (dualSymmetricSplit K) (universalBaseLocalized (K := K) 1)

def universalNativeTautologicalIsomorphism :
    (universalSymmetricGrassmannianLeft K).toSubmodule ≃ₗ[IsomChartRing K]
      (universalSymmetricGrassmannianRight K).toSubmodule :=
  (tensorTautologicalFrame K (IsomChartRing K) (symmetricSplit K)
    (universalBaseLocalized (K := K) 0)).symm.trans
      ((matrixLinearEquiv (IsomChartRing K) (universalIsomorphism (K := K))).trans
        (tensorTautologicalFrame K (IsomChartRing K) (dualSymmetricSplit K)
          (universalBaseLocalized (K := K) 1)))

/-- Pullback of the universal source plane by the native Grassmannian
functor. These are genuine algebraic-family base changes. -/
def symmetricLeftFamily (f : IsomChartRing K →ₐ[K] R) :
    Module.Grassmannian R (R ⊗[K] (M9.Symmetric3 K)) 2 :=
  Module.Grassmannian.map f (universalSymmetricGrassmannianLeft K)

def symmetricRightFamily (f : IsomChartRing K →ₐ[K] R) :
    Module.Grassmannian R (R ⊗[K] (Module.Dual K (M9.Symmetric3 K))) 2 :=
  Module.Grassmannian.map f (universalSymmetricGrassmannianRight K)

omit [Nontrivial R] in
theorem symmetricLeftFamily_baseChange {S : Type u} [CommRing S] [Algebra K S]
    (f : IsomChartRing K →ₐ[K] R) (g : R →ₐ[K] S) :
    symmetricLeftFamily K S (g.comp f) = Module.Grassmannian.map g (symmetricLeftFamily K R f) :=
  Module.Grassmannian.map_comp (k := 2) f g _

omit [Nontrivial R] in
theorem symmetricRightFamily_baseChange {S : Type u} [CommRing S] [Algebra K S]
    (f : IsomChartRing K →ₐ[K] R) (g : R →ₐ[K] S) :
    symmetricRightFamily K S (g.comp f) = Module.Grassmannian.map g (symmetricRightFamily K R f) :=
  Module.Grassmannian.map_comp (k := 2) f g _

end ActualSymmetricFibers

section DeterminantTransitions
variable (R : Type*) [CommRing R]
abbrev GL4 := Matrix.GeneralLinearGroup (Fin 4) R

/-- In a free rank-four frame, `S ⊗ (det S)∨` changes frame by this actual
unit matrix, defined over an arbitrary commutative coefficient ring. -/
def adjustedFrame (g : GL4 R) : GL4 R :=
  Matrix.GeneralLinearGroup.scalar (Fin 4) (Matrix.GeneralLinearGroup.det g)⁻¹ * g

theorem adjustedFrame_mul (g h : GL4 R) : adjustedFrame R (g*h) = adjustedFrame R g * adjustedFrame R h := by
  unfold adjustedFrame
  rw [map_mul, mul_inv_rev,
    mul_comm (Matrix.GeneralLinearGroup.det h)⁻¹ (Matrix.GeneralLinearGroup.det g)⁻¹, map_mul]
  simp only [mul_assoc]
  congr 1
  rw [← mul_assoc, Matrix.GeneralLinearGroup.scalar_commute, mul_assoc]

def adjustedFrameHom : GL4 R →* GL4 R where
  toFun := adjustedFrame R
  map_one' := by simp [adjustedFrame]
  map_mul' := adjustedFrame_mul R

theorem adjustedFrame_scalar_cubeRoot (a : Rˣ) (ha : a^3 = 1) :
    adjustedFrameHom R (Matrix.GeneralLinearGroup.scalar (Fin 4) a) = 1 := by
  change Matrix.GeneralLinearGroup.scalar (Fin 4)
    (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 4) a))⁻¹ *
      Matrix.GeneralLinearGroup.scalar (Fin 4) a = 1
  rw [Matrix.GeneralLinearGroup.det_scalar]
  simp only [Fintype.card_fin]
  have h4 : a^4 = a := by rw [show 4 = 3+1 by decide, pow_succ, ha, one_mul]
  rw [h4, ← map_mul, inv_mul_cancel, map_one]

theorem adjustedFrame_central_character (a : Rˣ) (ha : a^3 = 1) :
    adjustedFrameHom R (Matrix.GeneralLinearGroup.scalar (Fin 4) (a^2)) = 1 := by
  apply adjustedFrame_scalar_cubeRoot
  rw [← pow_mul, show 2*3 = 3*2 by decide, pow_mul, ha, one_pow]

/-- The actual overlap formula for a homomorphism between two framed
tautological rank-four modules. This is the cocycle compatibility required
to glue the determinant twist on the relative isomorphism chart. -/
theorem determinantTwist_frameChange (s t X : GL4 R) :
    adjustedFrameHom R (t⁻¹ * X * s) =
      (adjustedFrameHom R t)⁻¹ * adjustedFrameHom R X * adjustedFrameHom R s := by
  rw [map_mul, map_mul, map_inv]

theorem adjustedFrame_dual_central_character (a : Rˣ) (ha : a^3 = 1) :
    adjustedFrameHom R (Matrix.GeneralLinearGroup.scalar (Fin 4) ((a⁻¹)^2)) = 1 := by
  apply adjustedFrame_central_character
  rw [inv_pow, ha, inv_one]

def determinantDualLine (g : GL4 R) : R ≃ₗ[R] R :=
  LinearEquiv.smulOfUnit (M := R) (Matrix.GeneralLinearGroup.det g)⁻¹

theorem determinantLine_character (g : GL4 R) :
    LinearMap.det (matrixLinearEquiv R g).toLinearMap = g.val.det := by
  change LinearMap.det (Matrix.toLin' g.val) = g.val.det
  exact LinearMap.det_toLin' _

/-- The tensor action on the actual rank-four free module tensored with its
one-dimensional dual determinant frame. -/
def determinantTensorAction (g : GL4 R) :
    (Head R ⊗[R] R) ≃ₗ[R] (Head R ⊗[R] R) :=
  TensorProduct.congr (matrixLinearEquiv R g) (determinantDualLine R g)

theorem adjustedFrame_action (g : GL4 R) (x : Head R) :
    matrixLinearEquiv R (adjustedFrameHom R g) x =
      ((Matrix.GeneralLinearGroup.det g)⁻¹ : Rˣ) • matrixLinearEquiv R g x := by
  change (Matrix.scalar (Fin 4) ((Matrix.GeneralLinearGroup.det g)⁻¹ : Rˣ).val * g.val) *ᵥ x = _
  rw [← Matrix.mulVec_mulVec, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
    Matrix.smul_mulVec, Matrix.one_mulVec]
  rfl

/-- The tensor-product trivialization gives exactly the determinant-adjusted
transition matrix, rather than an unrelated rank-four representation. -/
theorem determinantTensorAction_trivialization (g : GL4 R) (v : Head R ⊗[R] R) :
    TensorProduct.rid R (Head R) (determinantTensorAction R g v) =
      matrixLinearEquiv R (adjustedFrameHom R g) (TensorProduct.rid R (Head R) v) := by
  induction v using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x a =>
    rw [determinantTensorAction, TensorProduct.congr_tmul, TensorProduct.rid_tmul,
      TensorProduct.rid_tmul, adjustedFrame_action]
    change (((Matrix.GeneralLinearGroup.det g)⁻¹ : Rˣ).val * a) • matrixLinearEquiv R g x =
      ((Matrix.GeneralLinearGroup.det g)⁻¹ : Rˣ).val • matrixLinearEquiv R g (a • x)
    rw [map_smul, smul_smul]

end DeterminantTransitions

section ActualCentralCharacters
variable (K : Type*) [Field K]

theorem symmetric_tautological_central_character (a : K) (ha : a^3 = 1)
    (A : BaseMatrix K) (x : Head K) :
    PrimitiveRepresentation.congruence K (PrimitiveRepresentation.centralElement K a ha).val
      (transportedCellFrame K (symmetricSplit K) A x).val =
      (transportedCellFrame K (symmetricSplit K) A (a^2 • x)).val := by
  rw [PrimitiveRepresentation.centralElement, PrimitiveRepresentation.congruence_scalar]
  exact (congrArg Subtype.val ((transportedCellFrame K (symmetricSplit K) A).map_smul (a^2) x)).symm

def centralDualAction (a : K) :
    Module.Dual K (M9.Symmetric3 K) →ₗ[K] Module.Dual K (M9.Symmetric3 K) :=
  (PrimitiveRepresentation.congruence K (a⁻¹ • (1 : Matrix (Fin 3) (Fin 3) K))).dualMap

theorem centralDualAction_eq (a : K) (f : Module.Dual K (M9.Symmetric3 K)) :
    centralDualAction K a f = (a⁻¹)^2 • f := by
  apply LinearMap.ext
  intro q
  simp only [centralDualAction, LinearMap.dualMap_apply,
    PrimitiveRepresentation.congruence_scalar, map_smul, smul_eq_mul]
  rfl

theorem dual_tautological_central_character (a : K) (B : BaseMatrix K) (x : Head K) :
    centralDualAction K a (transportedCellFrame K (dualSymmetricSplit K) B x).val =
      (transportedCellFrame K (dualSymmetricSplit K) B ((a⁻¹)^2 • x)).val := by
  rw [centralDualAction_eq]
  exact (congrArg Subtype.val
    ((transportedCellFrame K (dualSymmetricSplit K) B).map_smul ((a⁻¹)^2) x)).symm

end ActualCentralCharacters

theorem adjustedFrame_field_value {K : Type*} [Field K] (g : GL4 K) :
    (adjustedFrameHom K g).val = DeterminantTwist.twist g.val := by
  have hdet : ((Matrix.GeneralLinearGroup.det g)⁻¹ : Kˣ).val = g.val.det⁻¹ := by
    rw [Units.val_inv_eq_inv_val]
    rfl
  change Matrix.scalar (Fin 4) ((Matrix.GeneralLinearGroup.det g)⁻¹ : Kˣ).val * g.val = _
  rw [hdet, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  rfl

end M9.GraphBundleDescent
