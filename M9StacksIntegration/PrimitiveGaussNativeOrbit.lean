module

public import M9StacksIntegration.PrimitiveGaussFamily
public import M9StacksIntegration.NativeProjectiveLinear
public import M9StacksIntegration.NativeDominantFunctionField
public import M9.PrimitiveRadicalScheme
public import M9.ProjectiveFunctionField

/-! An actual dominant morphism to the native primitive projective space.
The constant change of coordinates is the proved equivalence with the frozen
fourteen-coordinate primitive basis. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 10000

open CategoryTheory AlgebraicGeometry Matrix MvPolynomial
open scoped BigOperators

namespace M9Native.PrimitiveGaussNativeOrbit

open M9.PrimitiveOpenOrbit M9.ExteriorPrimitive M9.PrimitiveRepresentation
open M9.ProjectiveFunctionField PrimitiveGaussCoordinates

def fullTuple : Primitive ℂ →ₗ[ℂ] (Fin 14 → ℂ) :=
  LinearMap.pi fun i => Fin.cases
    ((aCoordinate ℂ).comp (Primitive ℂ).subtype)
    (fun j => (coordinateFunctionals ℂ j).comp (Primitive ℂ).subtype) i

@[simp] theorem fullTuple_zero (w : Primitive ℂ) :
    fullTuple w 0 = aCoordinate ℂ w.val := rfl

@[simp] theorem fullTuple_succ (w : Primitive ℂ) (j : Fin 13) :
    fullTuple w j.succ = coordinateTuple ℂ w.val j := rfl

theorem fullTuple_injective : Function.Injective fullTuple := by
  intro u v h
  apply primitive_ext_tuple ℂ u v
  · exact congrFun h 0
  · funext j
    exact congrFun h j.succ

theorem fullTuple_bijective : Function.Bijective fullTuple := by
  refine ⟨fullTuple_injective, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (K := ℂ) (V := Primitive ℂ) (V₂ := Fin 14 → ℂ) (f := fullTuple)
    M9.PrimitiveRadicalScheme.primitiveCoordinates.finrank_eq).mp fullTuple_injective

def naturalCoordinates : Primitive ℂ ≃ₗ[ℂ] (Fin 14 → ℂ) :=
  LinearEquiv.ofBijective fullTuple fullTuple_bijective

def coordinateChange : (Fin 14 → ℂ) ≃ₗ[ℂ] (Fin 14 → ℂ) :=
  naturalCoordinates.symm.trans M9.PrimitiveRadicalScheme.primitiveCoordinates

def coordinateMatrix : Matrix.GeneralLinearGroup (Fin 14) ℂ :=
  NativeProjectiveLinear.coordinateGL ℂ 13 coordinateChange

theorem coordinateMatrix_mulVec (w : Primitive ℂ) :
    (coordinateMatrix : Matrix (Fin 14) (Fin 14) ℂ) *ᵥ fullTuple w =
      M9.PrimitiveRadicalScheme.primitiveCoordinates w := by
  rw [coordinateMatrix, NativeProjectiveLinear.coordinateGL_mulVec]
  exact M9.PrimitiveRadicalScheme.primitiveCoordinates.congr_arg
    (naturalCoordinates.symm_apply_apply w)

def polynomialTuple : Fin 14 → polynomial ℂ := Fin.cons (formalA ℂ) (formalTarget ℂ)

def polynomialVector : Fin 14 → polynomial ℂ :=
  (coordinateMatrix : Matrix (Fin 14) (Fin 14) ℂ).map MvPolynomial.C *ᵥ polynomialTuple

theorem eval_polynomialTuple (z : Fin 13 → ℂ) (ht : z 0 ≠ 0) :
    (fun i => MvPolynomial.eval z (polynomialTuple i)) = fullTuple (familyPrimitive ℂ z ht) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change MvPolynomial.eval z (formalA ℂ) = aCoordinate ℂ (familyPrimitive ℂ z ht).val
    exact (familyPrimitive_a ℂ z ht).symm
  · change MvPolynomial.eval z (formalTarget ℂ j) =
      coordinateTuple ℂ (familyPrimitive ℂ z ht).val j
    exact congrFun (familyPrimitive_tuple ℂ z ht).symm j

/-- The literal homogeneous vector of the scheme map is expressed in the exact
frozen primitive coordinates, rather than an abstract isomorphic fourteen-space. -/
theorem eval_polynomialVector (z : Fin 13 → ℂ) (ht : z 0 ≠ 0) :
    (fun i => MvPolynomial.eval z (polynomialVector i)) =
      M9.PrimitiveRadicalScheme.primitiveCoordinates (familyPrimitive ℂ z ht) := by
  funext i
  rw [polynomialVector, RingHom.map_mulVec]
  have hM : ((coordinateMatrix : Matrix (Fin 14) (Fin 14) ℂ).map MvPolynomial.C).map
      (MvPolynomial.eval z) = coordinateMatrix := by
    ext j k
    simp
  rw [hM]
  change ((coordinateMatrix : Matrix (Fin 14) (Fin 14) ℂ) *ᵥ
    (fun j => MvPolynomial.eval z (polynomialTuple j))) i = _
  rw [eval_polynomialTuple z ht, coordinateMatrix_mulVec]

abbrev source : Scheme := Spec (.of (sourceRing ℂ))

def naturalChart : Spec (.of (polynomial ℂ)) ⟶ space 13 :=
  Spec.map (CommRingCat.ofHom (chartCoordinatesEquiv 13 0).toRingHom) ≫ chartMap 13 0

instance naturalChart_isOpenImmersion : IsOpenImmersion naturalChart := by
  have : IsIso (CommRingCat.ofHom (chartCoordinatesEquiv 13 0).toRingHom) :=
    inferInstanceAs (IsIso (chartCoordinatesEquiv 13 0).toRingEquiv.toCommRingCatIso.hom)
  unfold naturalChart
  infer_instance

theorem naturalChart_dense : DenseRange naturalChart :=
  naturalChart.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)

instance naturalChart_isDominant : IsDominant naturalChart := ⟨naturalChart_dense⟩

def naturalMap : source ⟶ space 13 :=
  Spec.map (CommRingCat.ofHom (coordinateMap ℂ).toRingHom) ≫ naturalChart

instance naturalMap_isDominant : IsDominant naturalMap := by
  have : IsDominant (Spec.map (CommRingCat.ofHom (coordinateMap ℂ).toRingHom)) :=
    NativeDominantFunctionField.specMap_isDominant _ (coordinateMap_injective ℂ)
  unfold naturalMap
  infer_instance

def coordinateAutomorphism : space 13 ≅ space 13 :=
  NativeProjectiveLinear.projectiveLinear ℂ 13 coordinateMatrix

/-- A regular map from the honest principal-open Gauss parameter scheme to native P13. -/
def orbitMap : source ⟶ M9.ProjectiveGeometry.ProjectiveSpace.projectiveSpace 13 :=
  naturalMap ≫ coordinateAutomorphism.hom

/-- Dominance follows from the actual thirteen independent coordinate functions. -/
instance orbitMap_isDominant : IsDominant orbitMap := by
  unfold orbitMap
  infer_instance

theorem orbitMap_dense : DenseRange orbitMap := orbitMap.denseRange

end M9Native.PrimitiveGaussNativeOrbit
