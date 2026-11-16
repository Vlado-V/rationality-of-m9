module

public import M9StacksIntegration.GrassmannianCharts
public import M9.PrimitiveRadicalScheme
public import Mathlib.Data.Fin.Embedding
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# The actual forty-five cofactor coordinates on the native Grassmannian

The existing primitive cofactor polynomials are bound to the actual native
quotient chart of Gr9(14). Its last five columns are the quotient pivots,
so the existing [I9;X] frame uses exactly the native coordinate change X=-Y.
Each existing radical-component localization is therefore an actual open
in the native Grassmannian, with its original regular map to projective space.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 2048
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical TensorProduct Matrix

namespace M9Native.RadicalGrassmannianChart
open MvPolynomial AlgebraicGeometry.Grassmannian
open M9.RadicalMap M9.PrimitiveRadicalScheme

local instance primitiveGroup : AddCommGroup (M9.ExteriorPrimitive.Primitive ℂ) :=
  { (M9.ExteriorPrimitive.Primitive ℂ).addCommGroup with
    toAddCommMonoid := (M9.ExteriorPrimitive.Primitive ℂ).addCommMonoid }

def pivot : Fin 5 ↪ Fin 14 := Fin.natAddEmb 9
def head : Fin 9 ↪ Fin 14 := Fin.castLEEmb (by decide)

theorem head_notMem_pivot (j : Fin 9) : head j ∉ Set.range pivot := by
  rintro ⟨i,hi⟩
  have hv := congrArg Fin.val hi
  change 9+i.val = j.val at hv
  omega

theorem nonpivot_lt_nine (j : Fin 14) (hj : j ∉ Set.range pivot) : j.val < 9 := by
  by_contra h
  apply hj
  refine ⟨⟨j.val-9,by omega⟩,?_⟩
  apply Fin.ext
  change 9+(j.val-9) = j.val
  omega

def headComplementEquiv : Fin 9 ≃ {j : Fin 14 // j ∉ Set.range pivot} where
  toFun j := ⟨head j,head_notMem_pivot j⟩
  invFun j := ⟨j.val.val,nonpivot_lt_nine j.val j.property⟩
  left_inv _ := rfl
  right_inv j := by apply Subtype.ext; apply Fin.ext; rfl

abbrev NativeIndex := AlgebraicGeometry.Grassmannian.ChartIndex (k := 9) (n := 14) pivot

def coordinateIndexEquiv : NativeIndex ≃ M9.RadicalMap.ChartIndex :=
  (Equiv.ulift.trans (Equiv.prodCongr headComplementEquiv.symm (Equiv.refl (Fin 5)))).trans
    (Equiv.prodComm _ _)

abbrev nativePolynomial := GrassmannianCharts.chartPolynomial ℂ 9 14 pivot
abbrev parameterRing := M9.RadicalMap.ChartRing ℂ

def nativeToParameter : nativePolynomial →ₐ[ℂ] parameterRing :=
  aeval (fun a => -X (coordinateIndexEquiv a))

def parameterToNative : parameterRing →ₐ[ℂ] nativePolynomial :=
  aeval (fun a => -X (coordinateIndexEquiv.symm a))

/-- The sign is imposed by the actual native quotient matrix [Y|I5]. -/
def coordinateRingEquiv : nativePolynomial ≃ₐ[ℂ] parameterRing :=
  AlgEquiv.ofAlgHom nativeToParameter parameterToNative
    (by ext a; simp [nativeToParameter,parameterToNative])
    (by ext a; simp [nativeToParameter,parameterToNative])

@[simp] theorem coordinateRingEquiv_X (a : NativeIndex) :
    coordinateRingEquiv (X a) = -X (coordinateIndexEquiv a) := by
  simp [coordinateRingEquiv,nativeToParameter]

/-- The literal existing 45-variable parameter spectrum embeds as the
genuine matrix-chart open in the actual native Grassmannian. -/
def chart : Spec (.of parameterRing) ⟶ GrassmannianCharts.space ℂ 9 14 :=
  Spec.map (CommRingCat.ofHom coordinateRingEquiv.toRingHom) ≫
    GrassmannianCharts.chartSpecMap ℂ 9 14 pivot

instance chart_isOpenImmersion : IsOpenImmersion chart := by
  have : IsIso (CommRingCat.ofHom coordinateRingEquiv.toRingHom) :=
    coordinateRingEquiv.toRingEquiv.toCommRingCatIso.isIso_hom
  unfold chart
  infer_instance

theorem chart_dense : DenseRange chart :=
  chart.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)

@[reassoc] theorem chart_projection : chart ≫ GrassmannianCharts.projection ℂ 9 14 =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ parameterRing)) := by
  rw [chart,Category.assoc,GrassmannianCharts.chartSpecMap_projection,
    ← Spec.map_comp,← CommRingCat.ofHom_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact coordinateRingEquiv.toAlgHom.comp_algebraMap

/-- This actual generic-stalk field identification retains the original
forty-five cofactor-polynomial coordinates, including their native sign. -/
def functionFieldEquiv : (GrassmannianCharts.space ℂ 9 14).functionField ≃ₐ[ℂ]
    FractionRing parameterRing := by
  let e₁ := (GrassmannianCharts.openImmersionFunctionFieldIso chart).commRingCatIsoToRingEquiv
  let e₂ := (FractionRing.algEquiv parameterRing (Spec (.of parameterRing)).functionField).symm
  refine { __ := e₁.trans e₂.toRingEquiv, commutes' := fun c => ?_ }
  have h := GrassmannianCharts.openImmersionFunctionFieldIso_scalar ℂ chart
    (GrassmannianCharts.projection ℂ 9 14)
  rw [chart_projection,GrassmannianCharts.affine_structureScalarMap] at h
  have h₁ : e₁ (algebraMap ℂ (GrassmannianCharts.space ℂ 9 14).functionField c) =
      algebraMap parameterRing (Spec (.of parameterRing)).functionField
        (algebraMap ℂ parameterRing c) := DFunLike.congr_fun h c
  change e₂ (e₁ (algebraMap ℂ (GrassmannianCharts.space ℂ 9 14).functionField c)) = _
  rw [h₁,e₂.commutes]
  exact (IsScalarTower.algebraMap_apply ℂ parameterRing (FractionRing parameterRing) c).symm

/-- Every existing cofactor-component domain is now an actual native
Grassmannian open, not a stand-alone rational-function coordinate label. -/
def componentInclusion (j : Fin 9) (k : Fin 14) :
    Spec (.of (ComponentRing (radicalCoordinates j) k)) ⟶ GrassmannianCharts.space ℂ 9 14 :=
  componentSourceToChart (radicalCoordinates j) k ≫ chart

instance componentInclusion_isOpenImmersion (j : Fin 9) (k : Fin 14) :
    IsOpenImmersion (componentInclusion j k) := by
  unfold componentInclusion
  infer_instance

@[reassoc] theorem componentInclusion_projection (j : Fin 9) (k : Fin 14) :
    componentInclusion j k ≫ GrassmannianCharts.projection ℂ 9 14 =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (ComponentRing (radicalCoordinates j) k))) := by
  rw [componentInclusion,Category.assoc,chart_projection,componentSourceToChart,
    ← Spec.map_comp,← CommRingCat.ofHom_comp]
  congr 1

section Kernel
variable {R : Type*} [CommRing R]

def frameMatrix (D : Matrix (Fin 5) (Fin 9) R) : Matrix (Fin 14) (Fin 9) R :=
  fun i j => Sum.elim (fun k => if k = j then 1 else 0) (fun a => D a j)
    (finSumFinEquiv.symm i)

def quotientMatrix (D : Matrix (Fin 5) (Fin 9) R) : Matrix (Fin 5) (Fin 14) R :=
  fun i j => Sum.elim (fun k => -D i k) (fun k => if i = k then 1 else 0)
    (finSumFinEquiv.symm j)

@[simp] theorem frameMatrix_head (D : Matrix (Fin 5) (Fin 9) R) (i j : Fin 9) :
    frameMatrix D (head i) j = if i = j then 1 else 0 := by
  change Sum.elim _ _ (finSumFinEquiv.symm (Fin.castAdd 5 i)) = _
  simp only [finSumFinEquiv_symm_apply_castAdd,Sum.elim_inl]

@[simp] theorem frameMatrix_pivot (D : Matrix (Fin 5) (Fin 9) R) (i : Fin 5) (j : Fin 9) :
    frameMatrix D (pivot i) j = D i j := by
  change Sum.elim _ _ (finSumFinEquiv.symm (Fin.natAdd 9 i)) = _
  simp only [finSumFinEquiv_symm_apply_natAdd,Sum.elim_inr]

@[simp] theorem frameMatrix_mulVec_head (D : Matrix (Fin 5) (Fin 9) R)
    (v : Fin 9 → R) (i : Fin 9) : (frameMatrix D *ᵥ v) (head i) = v i := by
  simp [Matrix.mulVec,dotProduct]

@[simp] theorem frameMatrix_mulVec_pivot (D : Matrix (Fin 5) (Fin 9) R)
    (v : Fin 9 → R) (i : Fin 5) : (frameMatrix D *ᵥ v) (pivot i) = (D *ᵥ v) i := by
  simp only [Matrix.mulVec,dotProduct,frameMatrix_pivot]

theorem quotientMatrix_mulVec (D : Matrix (Fin 5) (Fin 9) R) (v : Fin 14 → R) :
    quotientMatrix D *ᵥ v = (v ∘ pivot) - D *ᵥ (v ∘ head) := by
  ext i
  simp only [Matrix.mulVec,dotProduct,Pi.sub_apply,Function.comp_apply]
  rw [Fin.sum_univ_add (a := 9) (b := 5)]
  simp only [quotientMatrix,finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd,Sum.elim_inl,Sum.elim_inr,ite_mul,
    one_mul,zero_mul,neg_mul,Finset.sum_neg_distrib]
  have hs : (∑ j : Fin 5,if i = j then v (Fin.natAdd 9 j) else 0) = v (Fin.natAdd 9 i) := by simp
  rw [hs]
  change -(∑ j : Fin 9,D i j*v (head j)) + v (pivot i) = v (pivot i) - ∑ j : Fin 9,D i j*v (head j)
  rw [sub_eq_add_neg,add_comm]

theorem quotientMatrix_ker (D : Matrix (Fin 5) (Fin 9) R) :
    (Matrix.toLin' (quotientMatrix D)).ker = (Matrix.toLin' (frameMatrix D)).range := by
  ext v
  change quotientMatrix D *ᵥ v = 0 ↔ _
  rw [quotientMatrix_mulVec,sub_eq_zero]
  constructor
  · intro hv
    refine ⟨v ∘ head,?_⟩
    change frameMatrix D *ᵥ (v ∘ head) = v
    ext j
    obtain ⟨r,rfl⟩ := (finSumFinEquiv : Fin 9 ⊕ Fin 5 ≃ Fin 14).surjective j
    rcases r with j | j
    · exact frameMatrix_mulVec_head D _ j
    · exact (frameMatrix_mulVec_pivot D _ j).trans (congrFun hv j).symm
  · rintro ⟨x,rfl⟩
    change ((frameMatrix D *ᵥ x) ∘ pivot) = D *ᵥ ((frameMatrix D *ᵥ x) ∘ head)
    have hh : (frameMatrix D *ᵥ x) ∘ head = x := funext (frameMatrix_mulVec_head D x)
    rw [hh]
    funext i
    exact frameMatrix_mulVec_pivot D x i

theorem quotientMatrix_eq_chartMatrix (D : Matrix (Fin 5) (Fin 9) R) :
    quotientMatrix D = chartMatrix (k := 9) (n := 14) pivot
      (fun a : NativeIndex => -D (coordinateIndexEquiv a).1 (coordinateIndexEquiv a).2) := by
  ext i j
  obtain ⟨r,rfl⟩ := (finSumFinEquiv : Fin 9 ⊕ Fin 5 ≃ Fin 14).surjective j
  rcases r with j | j
  · calc
      quotientMatrix D i ((finSumFinEquiv : Fin 9 ⊕ Fin 5 ≃ Fin 14) (.inl j)) = -D i j := by
        simp only [quotientMatrix,Equiv.symm_apply_apply,Sum.elim_inl]
      _ = chartMatrix (k := 9) (n := 14) pivot _ i (head j) := by
        symm
        exact chartMatrix_apply_of_notMem (k := 9) (n := 14) pivot
          (fun a : NativeIndex => -D (coordinateIndexEquiv a).1 (coordinateIndexEquiv a).2)
          i (head_notMem_pivot j)
  · calc
      quotientMatrix D i ((finSumFinEquiv : Fin 9 ⊕ Fin 5 ≃ Fin 14) (.inr j)) = if i = j then 1 else 0 := by
        simp only [quotientMatrix,Equiv.symm_apply_apply,Sum.elim_inr]
      _ = chartMatrix (k := 9) (n := 14) pivot _ i (pivot j) :=
        (chartMatrix_apply_self (k := 9) (n := 14) pivot _ i j).symm

end Kernel

theorem frameMatrix_eq_actual (x : M9.RadicalMap.ChartIndex → ℂ) :
    frameMatrix (fun i j => x (i,j)) =
      (chartFrameMatrix ℂ x).submatrix ambientFinEquiv.symm id := by
  ext i j
  obtain ⟨r,rfl⟩ := ambientFinEquiv.surjective i
  rcases r with i | i
  · simp only [Matrix.submatrix_apply,Equiv.symm_apply_apply,id_eq]
    exact (frameMatrix_head _ i j).trans (chartFrameMatrix_inl ℂ x i j).symm
  · simp only [Matrix.submatrix_apply,Equiv.symm_apply_apply,id_eq]
    exact (frameMatrix_pivot _ i j).trans (chartFrameMatrix_inr ℂ x i j).symm

theorem actualFrame_coordinates (x : M9.RadicalMap.ChartIndex → ℂ) (v : Fin 9 → ℂ) :
    primitiveCoordinates (frameMap (actualFrame x) v) = frameMatrix (fun i j => x (i,j)) *ᵥ v := by
  rw [frameMatrix_eq_actual]
  funext k
  exact basis_frameMap_chartFrame ℂ primitiveChartBasis x v (ambientFinEquiv.symm k)

/-- The native normalized quotient kernel is the image of the original
actual primitive nine-frame, under the fixed original primitive coordinates. -/
theorem quotient_kernel_actualFrame (x : M9.RadicalMap.ChartIndex → ℂ) :
    (Matrix.toLin' (quotientMatrix (fun i j => x (i,j)))).ker =
      (primitiveCoordinates.toLinearMap.comp (frameMap (actualFrame x))).range := by
  rw [quotientMatrix_ker]
  congr 1
  apply LinearMap.ext
  intro v
  exact (actualFrame_coordinates x v).symm

end M9Native.RadicalGrassmannianChart
