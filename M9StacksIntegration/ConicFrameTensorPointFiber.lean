module

public import M9StacksIntegration.GenericPointLiftsTensorProduct
public import M9StacksIntegration.ConicFramePointFiber

/-! The actual independent tensor product of the two conic coordinate
covers has 576 rational points in every nonempty fibre. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Algebra TensorProduct

namespace M9Native.ConicFrameTensorPointFiber

open ConicFrameSourceAlgebra ConicFrameExtension GenericPointLiftsTensorProduct

abbrev A := targetRing ℂ
abbrev B := sourceRing ℂ

def pairCoordinateMap : A ⊗[ℂ] A →ₐ[ℂ] B ⊗[ℂ] B :=
  Algebra.TensorProduct.map (coordinateMap ℂ) (coordinateMap ℂ)

@[instance_reducible] def pairCoordinateAlgebra : Algebra (A ⊗[ℂ] A) (B ⊗[ℂ] B) :=
  tensorCoordinateAlgebra (k := ℂ) (A₁ := A) (A₂ := A) (B₁ := B) (B₂ := B)

@[instance_reducible] def pairCoordinateTower :
    letI := pairCoordinateAlgebra
    IsScalarTower ℂ (A ⊗[ℂ] A) (B ⊗[ℂ] B) :=
  tensorCoordinateTower (k := ℂ) (A₁ := A) (A₂ := A) (B₁ := B) (B₂ := B)

theorem pairCoordinateMap_eq : pairCoordinateMap =
    tensorCoordinateMap (k := ℂ) (A₁ := A) (A₂ := A) (B₁ := B) (B₂ := B) := rfl

/-- A concrete equivalence of the actual algebra-map fibres, without
domain, linear-disjointness, or product-degree assumptions. -/
def pointLiftsEquiv (x : A ⊗[ℂ] A →ₐ[ℂ] ℂ) :
    letI := pairCoordinateAlgebra
    letI := pairCoordinateTower
    GenericEtaleFibreDegree.PointLifts ℂ (A ⊗[ℂ] A) (B ⊗[ℂ] B) x ≃
      GenericEtaleFibreDegree.PointLifts ℂ A B (restrictLeft x) ×
        GenericEtaleFibreDegree.PointLifts ℂ A B (restrictRight x) :=
  pointLiftsTensorProductEquiv (B₁ := B) (B₂ := B) x

/-- Both 24-point factors are the already proved actual conic-cover
fibres. The resulting 576-point claim has no fibre-count premise. -/
theorem card_pointLifts (x : A ⊗[ℂ] A →ₐ[ℂ] ℂ) :
    letI := pairCoordinateAlgebra
    letI := pairCoordinateTower
    Nonempty (GenericEtaleFibreDegree.PointLifts ℂ (A ⊗[ℂ] A) (B ⊗[ℂ] B) x) →
      Nat.card (GenericEtaleFibreDegree.PointLifts ℂ (A ⊗[ℂ] A) (B ⊗[ℂ] B) x) = 576 :=
  card_pointLifts_tensorProduct_24 ConicFramePointFiber.card_pointLifts
    ConicFramePointFiber.card_pointLifts x

end M9Native.ConicFrameTensorPointFiber
