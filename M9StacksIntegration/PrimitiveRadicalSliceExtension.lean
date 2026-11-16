module

public import M9StacksIntegration.PrimitiveRadicalSliceField
public import M9StacksIntegration.TensorFractionScalarExtension

@[expose] public section

/-! The actual native slice field is the coefficient field of the tensor-localized orbit
source. Its automorphisms extend by the identity on the original Gauss algebra. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace M9Native.PrimitiveRadicalSliceExtension

open PrimitiveRadicalOrbitFamily PrimitiveRadicalOrbitRings PrimitiveRadicalOrbitGenericPoints
open PrimitiveRadicalSliceField PrimitiveRhoFiberNondegenerate

abbrev SliceField := (GrassmannianCharts.space ℂ 4 12).functionField
abbrev SourceField := source.functionField

instance reducedMap_isOpenImmersion : IsOpenImmersion reducedMap := by
  unfold reducedMap
  infer_instance

instance reducedMap_isDominant : IsDominant reducedMap :=
  ⟨reducedMap.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

instance fiberProjection_isDominant : IsDominant fiberProjection := by
  unfold fiberProjection
  apply NativeDominantFunctionField.specMap_isDominant
  exact Algebra.TensorProduct.includeRight_injective (A := gaussRing) (B := fiberRing)
    (algebraMap ℂ gaussRing).injective

/-- This is induced by the actual nondegenerate open graph immersion and the actual affine
fraction inclusion. It retains the original native Grassmannian field. -/
def fiberFractionEquiv : SliceField ≃ₐ[ℂ] FractionRing fiberRing := by
  let e₁ := (GrassmannianCharts.openImmersionFunctionFieldIso reducedMap).commRingCatIsoToRingEquiv
  let e₂ := (FractionRing.algEquiv fiberRing nondegenerateDomain.functionField).symm
  refine { __ := e₁.trans e₂.toRingEquiv, commutes' := fun c => ?_ }
  have h := GrassmannianCharts.openImmersionFunctionFieldIso_scalar ℂ reducedMap
    (GrassmannianCharts.projection ℂ 4 12)
  rw [reducedMap_projection,GrassmannianCharts.affine_structureScalarMap] at h
  have hc : e₁ (algebraMap ℂ SliceField c) =
      algebraMap fiberRing nondegenerateDomain.functionField (algebraMap ℂ fiberRing c) :=
    DFunLike.congr_fun h c
  change e₂ (e₁ (algebraMap ℂ SliceField c)) = _
  rw [hc,e₂.commutes]
  exact (IsScalarTower.algebraMap_apply ℂ fiberRing (FractionRing fiberRing) c).symm

/-- The original fiber coordinate ring maps into the actual native slice generic stalk. -/
def fiberToSlice : fiberRing →ₐ[ℂ] SliceField :=
  fiberFractionEquiv.symm.toAlgHom.comp
    (IsScalarTower.toAlgHom ℂ fiberRing (FractionRing fiberRing))

@[simp] theorem fiberFractionEquiv_fiberToSlice (b : fiberRing) :
    fiberFractionEquiv (fiberToSlice b) = algebraMap fiberRing (FractionRing fiberRing) b :=
  fiberFractionEquiv.apply_symm_apply _

instance fiberAlgebra : Algebra fiberRing SliceField := fiberToSlice.toRingHom.toAlgebra

instance fiberScalarTower : IsScalarTower ℂ fiberRing SliceField :=
  IsScalarTower.of_algHom fiberToSlice

instance fiberIsFractionRing : IsFractionRing fiberRing SliceField := by
  let e : FractionRing fiberRing ≃ₐ[fiberRing] SliceField :=
    { __ := fiberFractionEquiv.symm.toRingEquiv
      commutes' b := rfl }
  exact IsFractionRing.of_algEquiv e

instance sourceCoordinateTower : IsScalarTower ℂ coordinateRing SourceField := by
  refine ⟨?_⟩
  intro (c : ℂ) (t : coordinateRing) (e : SourceField)
  have ht : c • t = coefficientMap c * t := by
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      change (c • a) ⊗ₜ[ℂ] b = _
      change (c • a) ⊗ₜ[ℂ] b =
        ((algebraMap ℂ gaussRing c) ⊗ₜ[ℂ] (1 : fiberRing)) * (a ⊗ₜ[ℂ] b)
      rw [Algebra.TensorProduct.tmul_mul_tmul,one_mul]
      rw [Algebra.smul_def]
    | add x y hx hy =>
      simp only [smul_add,hx,hy]
      exact ((Algebra.TensorProduct.mul (coefficientMap c)).map_add x y).symm
  change coordinateEmbedding (c • t) * e =
    algebraMap ℂ SourceField c * (coordinateEmbedding t * e)
  rw [ht,map_mul,coordinateEmbedding.commutes,mul_assoc]

theorem reducedMap_pullback_fiberToSlice (b : fiberRing) :
    NativeDominantFunctionField.map reducedMap (fiberToSlice b) =
      algebraMap fiberRing nondegenerateDomain.functionField b := by
  let e₁ := (GrassmannianCharts.openImmersionFunctionFieldIso reducedMap).commRingCatIsoToRingEquiv
  let e₂ := (FractionRing.algEquiv fiberRing nondegenerateDomain.functionField).symm
  have h := fiberFractionEquiv_fiberToSlice b
  change e₂ (e₁ (fiberToSlice b)) = algebraMap fiberRing (FractionRing fiberRing) b at h
  have he : e₁ (fiberToSlice b) = algebraMap fiberRing nondegenerateDomain.functionField b :=
    e₂.injective (h.trans (e₂.commutes b).symm)
  have ho : (GrassmannianCharts.openImmersionFunctionFieldIso reducedMap).hom.hom =
      NativeDominantFunctionField.map reducedMap := by
    simp only [GrassmannianCharts.openImmersionFunctionFieldIso,NativeDominantFunctionField.map,
      CategoryTheory.Iso.trans_hom,asIso_hom]
  rw [← ho]
  exact he

/-- The coefficient inclusion is identified with the original native slice pullback on every
actual fiber-ring coordinate, by functoriality of the genuine generic-stalk maps. -/
theorem sliceEmbedding_fiberToSlice (b : fiberRing) :
    sliceEmbedding (fiberToSlice b) = coordinateEmbedding ((1 : gaussRing) ⊗ₜ[ℂ] b) := by
  haveI : IsDominant (Spec.map (CommRingCat.ofHom (R := fiberRing) (S := coordinateRing)
      (Algebra.TensorProduct.includeRight : fiberRing →ₐ[ℂ] coordinateRing).toRingHom)) :=
    fiberProjection_isDominant
  change NativeDominantFunctionField.map (fiberProjection ≫ reducedMap) (fiberToSlice b) = _
  rw [NativeFunctionFieldFunctor.map_comp,RingHom.comp_apply,reducedMap_pullback_fiberToSlice]
  change NativeDominantFunctionField.map
    (Spec.map (CommRingCat.ofHom (R := fiberRing) (S := coordinateRing)
      (Algebra.TensorProduct.includeRight : fiberRing →ₐ[ℂ] coordinateRing).toRingHom))
      (algebraMap fiberRing nondegenerateDomain.functionField b) =
        algebraMap coordinateRing SourceField ((1 : gaussRing) ⊗ₜ[ℂ] b)
  exact NativeFunctionFieldFunctor.affine_map_algebraMap _ b

theorem rightEmbedding_eq_sliceEmbedding :
    TensorFractionScalarExtension.rightEmbedding ℂ gaussRing fiberRing SliceField SourceField =
      sliceEmbedding := by
  have h : (TensorFractionScalarExtension.rightEmbedding ℂ gaussRing fiberRing SliceField SourceField).toRingHom =
      sliceEmbedding.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := fiberRing)
    intro b
    change TensorFractionScalarExtension.rightEmbedding ℂ gaussRing fiberRing SliceField SourceField
      (algebraMap fiberRing SliceField b) = sliceEmbedding (algebraMap fiberRing SliceField b)
    rw [TensorFractionScalarExtension.rightEmbedding_algebraMap]
    exact (sliceEmbedding_fiberToSlice b).symm
  ext f
  exact DFunLike.congr_fun h f

instance coefficientTensor_isDomain : IsDomain (gaussRing ⊗[ℂ] SliceField) :=
  TensorFractionScalarExtension.localizedRing_isDomain ℂ gaussRing fiberRing SliceField

/-- The original source generic stalk is the genuine fraction field of the tensor product
with its actual native slice coefficient field. -/
def coefficientTensorEquiv : SourceField ≃ₐ[ℂ] FractionRing (gaussRing ⊗[ℂ] SliceField) :=
  TensorFractionScalarExtension.comparison ℂ gaussRing fiberRing SliceField SourceField

@[simp] theorem coefficientTensorEquiv_slice (f : SliceField) :
    coefficientTensorEquiv (sliceEmbedding f) =
      algebraMap (gaussRing ⊗[ℂ] SliceField) (FractionRing (gaussRing ⊗[ℂ] SliceField))
        ((1 : gaussRing) ⊗ₜ[ℂ] f) := by
  have h := TensorFractionScalarExtension.comparison_right ℂ gaussRing fiberRing SliceField SourceField f
  rw [rightEmbedding_eq_sliceEmbedding] at h
  exact h

@[simp] theorem coefficientTensorEquiv_gauss (a : gaussRing) :
    coefficientTensorEquiv (coordinateEmbedding (a ⊗ₜ[ℂ] (1 : fiberRing))) =
      algebraMap (gaussRing ⊗[ℂ] SliceField) (FractionRing (gaussRing ⊗[ℂ] SliceField))
        (a ⊗ₜ[ℂ] (1 : SliceField)) :=
  TensorFractionScalarExtension.comparison_left ℂ gaussRing fiberRing SliceField SourceField a

/-- Any actual automorphism of the native slice field extends by the identity on the original
Gauss algebra, including every actual constant stabilizer automorphism. -/
def sourceExtension (σ : SliceField ≃ₐ[ℂ] SliceField) : SourceField ≃ₐ[ℂ] SourceField :=
  TensorFractionScalarExtension.sourceExtension ℂ gaussRing fiberRing SliceField SourceField σ

@[simp] theorem sourceExtension_slice (σ : SliceField ≃ₐ[ℂ] SliceField) (f : SliceField) :
    sourceExtension σ (sliceEmbedding f) = sliceEmbedding (σ f) := by
  have h := TensorFractionScalarExtension.sourceExtension_right
    ℂ gaussRing fiberRing SliceField SourceField σ f
  rw [rightEmbedding_eq_sliceEmbedding] at h
  exact h

@[simp] theorem sourceExtension_gauss (σ : SliceField ≃ₐ[ℂ] SliceField) (a : gaussRing) :
    sourceExtension σ (coordinateEmbedding (a ⊗ₜ[ℂ] (1 : fiberRing))) =
      coordinateEmbedding (a ⊗ₜ[ℂ] (1 : fiberRing)) :=
  TensorFractionScalarExtension.sourceExtension_left ℂ gaussRing fiberRing SliceField SourceField σ a

end M9Native.PrimitiveRadicalSliceExtension
