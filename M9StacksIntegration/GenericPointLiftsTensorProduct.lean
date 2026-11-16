module

public import M9StacksIntegration.GenericEtaleFibreDegree
public import Mathlib.RingTheory.TensorProduct.Maps

/-! Actual rational-point fibres of a tensor product of algebra maps.
The decomposition follows from the algebra tensor-product universal
property; no geometric fibre correspondence or product degree is assumed. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Algebra TensorProduct

namespace M9Native.GenericPointLiftsTensorProduct

variable {k A₁ A₂ B₁ B₂ : Type*} [Field k]
  [CommRing A₁] [CommRing A₂] [CommRing B₁] [CommRing B₂]
  [Algebra k A₁] [Algebra k A₂] [Algebra k B₁] [Algebra k B₂]

def restrictLeft (x : A₁ ⊗[k] A₂ →ₐ[k] k) : A₁ →ₐ[k] k :=
  x.comp Algebra.TensorProduct.includeLeft

def restrictRight (x : A₁ ⊗[k] A₂ →ₐ[k] k) : A₂ →ₐ[k] k :=
  x.comp Algebra.TensorProduct.includeRight

/-- The genuine algebra tensor-product universal property for rational
points, with both restrictions specified by the actual tensor inclusions. -/
def tensorAlgHomEquiv : (B₁ ⊗[k] B₂ →ₐ[k] k) ≃
    (B₁ →ₐ[k] k) × (B₂ →ₐ[k] k) where
  toFun y := (restrictLeft y,restrictRight y)
  invFun y := Algebra.TensorProduct.lift y.1 y.2 (fun _ _ => Commute.all _ _)
  left_inv y := by
    apply Algebra.TensorProduct.ext'
    intro b₁ b₂
    change y (b₁ ⊗ₜ[k] 1) * y (1 ⊗ₜ[k] b₂) = y (b₁ ⊗ₜ[k] b₂)
    rw [← map_mul,TensorProduct.tmul_mul_tmul,mul_one,one_mul]
  right_inv y := by
    apply Prod.ext
    · exact Algebra.TensorProduct.lift_comp_includeLeft _ _ _
    · exact Algebra.TensorProduct.lift_comp_includeRight' _ _ _

/-- Actual lifts under a named algebra homomorphism. This is the literal
subtype used by `GenericEtaleFibreDegree.PointLifts`, before its algebra
map is bundled into a typeclass. -/
def MappedPointLifts (f : A₁ →ₐ[k] B₁) (x : A₁ →ₐ[k] k) :=
  { y : B₁ →ₐ[k] k // y.comp f = x }

def tensorMap (f₁ : A₁ →ₐ[k] B₁) (f₂ : A₂ →ₐ[k] B₂) :
    A₁ ⊗[k] A₂ →ₐ[k] B₁ ⊗[k] B₂ :=
  Algebra.TensorProduct.map f₁ f₂

/-- The actual tensor-cover fibre is the product of the two actual
restricted fibres. Both directions are constructed from algebra maps. -/
def mappedPointLiftsTensorProductEquiv
    (f₁ : A₁ →ₐ[k] B₁) (f₂ : A₂ →ₐ[k] B₂) (x : A₁ ⊗[k] A₂ →ₐ[k] k) :
    MappedPointLifts (tensorMap f₁ f₂) x ≃
      MappedPointLifts f₁ (restrictLeft x) × MappedPointLifts f₂ (restrictRight x) where
  toFun y :=
    (⟨restrictLeft y.val,by
      have h := congrArg (fun z : A₁ ⊗[k] A₂ →ₐ[k] k =>
        z.comp Algebra.TensorProduct.includeLeft) y.property
      simpa only [restrictLeft,tensorMap,AlgHom.comp_assoc,
        Algebra.TensorProduct.map_comp_includeLeft] using h⟩,
     ⟨restrictRight y.val,by
      have h := congrArg (fun z : A₁ ⊗[k] A₂ →ₐ[k] k =>
        z.comp Algebra.TensorProduct.includeRight) y.property
      simpa only [restrictRight,tensorMap,AlgHom.comp_assoc,
        Algebra.TensorProduct.map_comp_includeRight] using h⟩)
  invFun y := ⟨Algebra.TensorProduct.lift y.1.val y.2.val (fun _ _ => Commute.all _ _),by
    apply Algebra.TensorProduct.ext'
    intro a₁ a₂
    change y.1.val (f₁ a₁) * y.2.val (f₂ a₂) = x (a₁ ⊗ₜ[k] a₂)
    have h₁ : y.1.val (f₁ a₁) = restrictLeft x a₁ :=
      DFunLike.congr_fun y.1.property a₁
    have h₂ : y.2.val (f₂ a₂) = restrictRight x a₂ :=
      DFunLike.congr_fun y.2.property a₂
    rw [h₁,h₂]
    change x (a₁ ⊗ₜ[k] 1) * x (1 ⊗ₜ[k] a₂) = x (a₁ ⊗ₜ[k] a₂)
    rw [← map_mul,TensorProduct.tmul_mul_tmul,mul_one,one_mul]⟩
  left_inv y := by
    apply Subtype.ext
    exact tensorAlgHomEquiv.left_inv y.val
  right_inv y := by
    apply Prod.ext
    · apply Subtype.ext
      exact Algebra.TensorProduct.lift_comp_includeLeft _ _ (fun _ _ => Commute.all _ _)
    · apply Subtype.ext
      exact Algebra.TensorProduct.lift_comp_includeRight' _ _ (fun _ _ => Commute.all _ _)

/-- The actual algebra structure attached to the tensor product of the
two named coordinate homomorphisms. It is not installed globally. -/
@[instance_reducible] def tensorMapAlgebra (f₁ : A₁ →ₐ[k] B₁) (f₂ : A₂ →ₐ[k] B₂) :
    Algebra (A₁ ⊗[k] A₂) (B₁ ⊗[k] B₂) :=
  (tensorMap f₁ f₂).toRingHom.toAlgebra

@[instance_reducible] def tensorMapTower (f₁ : A₁ →ₐ[k] B₁) (f₂ : A₂ →ₐ[k] B₂) :
    letI := tensorMapAlgebra f₁ f₂
    IsScalarTower k (A₁ ⊗[k] A₂) (B₁ ⊗[k] B₂) := by
  letI := tensorMapAlgebra f₁ f₂
  exact IsScalarTower.of_algebraMap_eq' (tensorMap f₁ f₂).comp_algebraMap.symm

section Towers

variable [Algebra A₁ B₁] [Algebra A₂ B₂]
  [IsScalarTower k A₁ B₁] [IsScalarTower k A₂ B₂]

def tensorCoordinateMap : A₁ ⊗[k] A₂ →ₐ[k] B₁ ⊗[k] B₂ :=
  tensorMap (IsScalarTower.toAlgHom k A₁ B₁) (IsScalarTower.toAlgHom k A₂ B₂)

@[instance_reducible] def tensorCoordinateAlgebra : Algebra (A₁ ⊗[k] A₂) (B₁ ⊗[k] B₂) :=
  tensorMapAlgebra (IsScalarTower.toAlgHom k A₁ B₁) (IsScalarTower.toAlgHom k A₂ B₂)

@[instance_reducible] def tensorCoordinateTower :
    letI := tensorCoordinateAlgebra (k := k) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
    IsScalarTower k (A₁ ⊗[k] A₂) (B₁ ⊗[k] B₂) :=
  tensorMapTower (IsScalarTower.toAlgHom k A₁ B₁) (IsScalarTower.toAlgHom k A₂ B₂)

/-- The tensor-product decomposition for the original `PointLifts`
subtypes under the explicit tensor-coordinate algebra and scalar tower. -/
def pointLiftsTensorProductEquiv (x : A₁ ⊗[k] A₂ →ₐ[k] k) :
    letI := tensorCoordinateAlgebra (k := k) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
    letI := tensorCoordinateTower (k := k) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
    GenericEtaleFibreDegree.PointLifts k (A₁ ⊗[k] A₂) (B₁ ⊗[k] B₂) x ≃
      GenericEtaleFibreDegree.PointLifts k A₁ B₁ (restrictLeft x) ×
        GenericEtaleFibreDegree.PointLifts k A₂ B₂ (restrictRight x) :=
  mappedPointLiftsTensorProductEquiv
    (IsScalarTower.toAlgHom k A₁ B₁) (IsScalarTower.toAlgHom k A₂ B₂) x

theorem card_pointLifts_tensorProduct (N₁ N₂ : ℕ)
    (h₁ : ∀ x₁ : A₁ →ₐ[k] k,
      Nonempty (GenericEtaleFibreDegree.PointLifts k A₁ B₁ x₁) →
      Nat.card (GenericEtaleFibreDegree.PointLifts k A₁ B₁ x₁) = N₁)
    (h₂ : ∀ x₂ : A₂ →ₐ[k] k,
      Nonempty (GenericEtaleFibreDegree.PointLifts k A₂ B₂ x₂) →
      Nat.card (GenericEtaleFibreDegree.PointLifts k A₂ B₂ x₂) = N₂)
    (x : A₁ ⊗[k] A₂ →ₐ[k] k) :
    letI := tensorCoordinateAlgebra (k := k) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
    letI := tensorCoordinateTower (k := k) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
    Nonempty (GenericEtaleFibreDegree.PointLifts k (A₁ ⊗[k] A₂) (B₁ ⊗[k] B₂) x) →
      Nat.card (GenericEtaleFibreDegree.PointLifts k (A₁ ⊗[k] A₂) (B₁ ⊗[k] B₂) x) = N₁ * N₂ := by
  letI := tensorCoordinateAlgebra (k := k) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
  letI := tensorCoordinateTower (k := k) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
  intro hne
  let e := pointLiftsTensorProductEquiv (B₁ := B₁) (B₂ := B₂) x
  have hp := hne.map e
  rw [Nat.card_congr e,Nat.card_prod,h₁ _ (hp.map Prod.fst),h₂ _ (hp.map Prod.snd)]

theorem card_pointLifts_tensorProduct_24
    (h₁ : ∀ x₁ : A₁ →ₐ[k] k,
      Nonempty (GenericEtaleFibreDegree.PointLifts k A₁ B₁ x₁) →
      Nat.card (GenericEtaleFibreDegree.PointLifts k A₁ B₁ x₁) = 24)
    (h₂ : ∀ x₂ : A₂ →ₐ[k] k,
      Nonempty (GenericEtaleFibreDegree.PointLifts k A₂ B₂ x₂) →
      Nat.card (GenericEtaleFibreDegree.PointLifts k A₂ B₂ x₂) = 24)
    (x : A₁ ⊗[k] A₂ →ₐ[k] k) :
    letI := tensorCoordinateAlgebra (k := k) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
    letI := tensorCoordinateTower (k := k) (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂)
    Nonempty (GenericEtaleFibreDegree.PointLifts k (A₁ ⊗[k] A₂) (B₁ ⊗[k] B₂) x) →
      Nat.card (GenericEtaleFibreDegree.PointLifts k (A₁ ⊗[k] A₂) (B₁ ⊗[k] B₂) x) = 576 := by
  simpa using card_pointLifts_tensorProduct 24 24 h₁ h₂ x

end Towers

end M9Native.GenericPointLiftsTensorProduct
