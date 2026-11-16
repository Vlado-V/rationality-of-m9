module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Localizing one tensor factor to its actual fraction field preserves the fraction field
of the tensor product. Scalar automorphisms then extend by the identity on the other factor. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open scoped TensorProduct

namespace M9Native.TensorFractionScalarExtension

variable (k A B F E : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
  [CommRing B] [IsDomain B] [Algebra k B] [Field F] [Algebra k F] [Algebra B F]
  [IsScalarTower k B F] [IsFractionRing B F]
  [Field E] [Algebra k E] [Algebra (A ⊗[k] B) E]
  [IsScalarTower k (A ⊗[k] B) E] [IsFractionRing (A ⊗[k] B) E]
  [IsDomain (A ⊗[k] B)]

attribute [local instance] Module.Free.of_divisionRing Module.Flat.of_free

abbrev sourceRing := A ⊗[k] B
abbrev localizedRing := A ⊗[k] F

def tensorMap : sourceRing k A B →ₐ[k] localizedRing k A F :=
  Algebra.TensorProduct.map (AlgHom.id k A) (IsScalarTower.toAlgHom k B F)

instance tensorAlgebra : Algebra (sourceRing k A B) (localizedRing k A F) :=
  (tensorMap k A B F).toRingHom.toAlgebra

instance tensorLeftTower : IsScalarTower A (sourceRing k A B) (localizedRing k A F) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro a
  change a ⊗ₜ[k] (1 : F) = tensorMap k A B F (a ⊗ₜ[k] (1 : B))
  simp only [tensorMap,Algebra.TensorProduct.map_tmul,AlgHom.id_apply,map_one]

instance tensorScalarTower : IsScalarTower k (sourceRing k A B) (localizedRing k A F) :=
  IsScalarTower.of_algHom (tensorMap k A B F)

def denominators : Submonoid (sourceRing k A B) :=
  (nonZeroDivisors B).map (Algebra.TensorProduct.includeRight (R := k) (A := A))

instance tensorLocalization : IsLocalization (denominators k A B) (localizedRing k A F) := by
  apply IsLocalization.tensorProduct_tensorProduct_right k A (nonZeroDivisors B) F
  apply RingHom.ext
  intro b
  change tensorMap k A B F ((1 : A) ⊗ₜ[k] b) = (1 : A) ⊗ₜ[k] algebraMap B F b
  simp only [tensorMap,Algebra.TensorProduct.map_tmul,map_one,AlgHom.id_apply]
  rfl

theorem denominators_regular : denominators k A B ≤ nonZeroDivisors (sourceRing k A B) := by
  rintro x ⟨b,hb,rfl⟩
  rw [mem_nonZeroDivisors_iff_ne_zero]
  have hi := Algebra.TensorProduct.includeRight_injective (A := A) (B := B)
    (algebraMap k A).injective
  simpa only [map_zero] using hi.ne (nonZeroDivisors.ne_zero hb)

include B in
theorem localizedRing_isDomain : IsDomain (localizedRing k A F) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (localizedRing k A F) (denominators_regular k A B)

def leftEmbedding : A →ₐ[k] E :=
  (IsScalarTower.toAlgHom k (sourceRing k A B) E).comp Algebra.TensorProduct.includeLeft

def rightBaseEmbedding : B →ₐ[k] E :=
  (IsScalarTower.toAlgHom k (sourceRing k A B) E).comp Algebra.TensorProduct.includeRight

theorem rightBaseEmbedding_injective : Function.Injective (rightBaseEmbedding k A B E) :=
  (IsFractionRing.injective (sourceRing k A B) E).comp
    (Algebra.TensorProduct.includeRight_injective (A := A) (B := B) (algebraMap k A).injective)

/-- The unique actual extension of the original right tensor factor to its fraction field. -/
def rightEmbedding : F →ₐ[k] E :=
  IsFractionRing.liftAlgHom (rightBaseEmbedding_injective k A B E)

@[simp] theorem rightEmbedding_algebraMap (b : B) :
    rightEmbedding k A B F E (algebraMap B F b) = rightBaseEmbedding k A B E b :=
  IsFractionRing.lift_algebraMap (rightBaseEmbedding_injective k A B E) b

def tensorEmbedding : localizedRing k A F →ₐ[k] E :=
  Algebra.TensorProduct.lift (leftEmbedding k A B E) (rightEmbedding k A B F E)
    (fun _ _ => Commute.all _ _)

@[simp] theorem tensorEmbedding_tmul (a : A) (f : F) :
    tensorEmbedding k A B F E (a ⊗ₜ[k] f) =
      leftEmbedding k A B E a * rightEmbedding k A B F E f := by
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

theorem tensorEmbedding_comp :
    (tensorEmbedding k A B F E).comp (tensorMap k A B F) =
      IsScalarTower.toAlgHom k (sourceRing k A B) E := by
  apply Algebra.TensorProduct.ext'
  intro a b
  simp only [AlgHom.comp_apply,tensorMap,Algebra.TensorProduct.map_tmul,AlgHom.id_apply,
    tensorEmbedding_tmul]
  change leftEmbedding k A B E a * rightEmbedding k A B F E (algebraMap B F b) =
    algebraMap (sourceRing k A B) E (a ⊗ₜ[k] b)
  rw [rightEmbedding_algebraMap]
  change algebraMap (sourceRing k A B) E (a ⊗ₜ[k] (1 : B)) *
    algebraMap (sourceRing k A B) E ((1 : A) ⊗ₜ[k] b) = _
  rw [← map_mul,Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]

@[instance_reducible] def localizedSourceAlgebra : Algebra (localizedRing k A F) E :=
  (tensorEmbedding k A B F E).toRingHom.toAlgebra

theorem localizedSourceScalarTower :
    letI := localizedSourceAlgebra k A B F E
    IsScalarTower k (localizedRing k A F) E := by
  letI := localizedSourceAlgebra k A B F E
  exact IsScalarTower.of_algHom (tensorEmbedding k A B F E)

theorem sourceLocalizationTower :
    letI := localizedSourceAlgebra k A B F E
    IsScalarTower (sourceRing k A B) (localizedRing k A F) E := by
  letI := localizedSourceAlgebra k A B F E
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro x
  exact (DFunLike.congr_fun (tensorEmbedding_comp k A B F E) x).symm

theorem source_isFractionRing :
    letI := localizedSourceAlgebra k A B F E
    IsFractionRing (localizedRing k A F) E := by
  letI := localizedSourceAlgebra k A B F E
  haveI := sourceLocalizationTower k A B F E
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (denominators k A B) (localizedRing k A F) E

/-- The isomorphism is induced by the original tensor-localization map into the original
source field, rather than an independently chosen rational-field identification. -/
def comparison : E ≃ₐ[k] FractionRing (localizedRing k A F) := by
  letI := localizedSourceAlgebra k A B F E
  haveI := localizedSourceScalarTower k A B F E
  haveI := source_isFractionRing k A B F E
  exact ((FractionRing.algEquiv (localizedRing k A F) E).symm).restrictScalars k

@[simp] theorem comparison_tensorEmbedding (x : localizedRing k A F) :
    comparison k A B F E (tensorEmbedding k A B F E x) =
      algebraMap (localizedRing k A F) (FractionRing (localizedRing k A F)) x := by
  letI := localizedSourceAlgebra k A B F E
  haveI := localizedSourceScalarTower k A B F E
  haveI := source_isFractionRing k A B F E
  exact ((FractionRing.algEquiv (localizedRing k A F) E).symm).commutes x

@[simp] theorem comparison_right (f : F) :
    comparison k A B F E (rightEmbedding k A B F E f) =
      algebraMap (localizedRing k A F) (FractionRing (localizedRing k A F)) ((1 : A) ⊗ₜ[k] f) := by
  have h := comparison_tensorEmbedding k A B F E ((1 : A) ⊗ₜ[k] f)
  simpa only [tensorEmbedding_tmul,map_one,one_mul] using h

@[simp] theorem comparison_left (a : A) :
    comparison k A B F E (leftEmbedding k A B E a) =
      algebraMap (localizedRing k A F) (FractionRing (localizedRing k A F)) (a ⊗ₜ[k] (1 : F)) := by
  have h := comparison_tensorEmbedding k A B F E (a ⊗ₜ[k] (1 : F))
  simpa only [tensorEmbedding_tmul,map_one,mul_one] using h

/-- Every coefficient-field automorphism extends by the identity on the actual left factor. -/
def sourceExtension (σ : F ≃ₐ[k] F) : E ≃ₐ[k] E :=
  (comparison k A B F E).trans
    ((IsFractionRing.algEquivOfAlgEquiv
      (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[k] A) σ)).trans
        (comparison k A B F E).symm)

@[simp] theorem sourceExtension_right (σ : F ≃ₐ[k] F) (f : F) :
    sourceExtension k A B F E σ (rightEmbedding k A B F E f) =
      rightEmbedding k A B F E (σ f) := by
  apply (comparison k A B F E).injective
  simp only [sourceExtension,AlgEquiv.trans_apply,AlgEquiv.apply_symm_apply,
    comparison_right,IsFractionRing.algEquivOfAlgEquiv_algebraMap,
    Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul,
    AlgEquiv.coe_toAlgHom,AlgEquiv.coe_refl,id_eq,map_one]

@[simp] theorem sourceExtension_left (σ : F ≃ₐ[k] F) (a : A) :
    sourceExtension k A B F E σ (leftEmbedding k A B E a) = leftEmbedding k A B E a := by
  apply (comparison k A B F E).injective
  simp only [sourceExtension,AlgEquiv.trans_apply,AlgEquiv.apply_symm_apply,
    comparison_left,IsFractionRing.algEquivOfAlgEquiv_algebraMap,
    Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul,
    AlgEquiv.coe_toAlgHom,AlgEquiv.coe_refl,id_eq,map_one]

end M9Native.TensorFractionScalarExtension
