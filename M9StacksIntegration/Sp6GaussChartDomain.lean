module

public import M9StacksIntegration.Sp6AffineBaseChange
public import M9StacksIntegration.Sp6GaussCellCoordinates
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Domain of the genuine Gauss parameter ring after every field base change

The actual parameter ring is polynomial in twelve variables over the
actual GL3 determinant localization. Native tensor/polynomial and
tensor/localization equivalences prove that its actual base change
over the original integer base is a domain over every field.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace M9Native.Sp6GaussChartDomain

open Sp6AffineBaseChange (IntegerRing tensorObject tensorObjectLeftAlgebra)

def tensorRightElement (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (t : T) : tensorObject R S T :=
  Algebra.TensorProduct.includeRight t

def tensorEvaluation (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (f : T →ₐ[R] S) : tensorObject R S T →+* S :=
  (AlgHom.liftEquiv R S T S f).toRingHom

theorem tensorEvaluation_rightElement (R S T : Type u)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (f : T →ₐ[R] S) (t : T) :
    tensorEvaluation R S T f (tensorRightElement R S T t) = f t := by
  change ((AlgHom.liftEquiv R S T S) f) (1 ⊗ₜ[R] t) = f t
  exact (AlgHom.liftEquiv_tmul f (1 : S) t).trans (one_smul S (f t))

abbrev LinearPolynomial : Type u := MvPolynomial (Fin 3 × Fin 3) IntegerRing.{u}

variable (K : Type u) [Field K]

local instance targetIntegerAlgebra : Algebra IntegerRing.{u} K :=
  Sp6AffineBaseChange.integerAlgebra K

abbrev PolynomialCoordinateRing : Type u :=
  tensorObject IntegerRing.{u} K LinearPolynomial.{u}

instance polynomialCommRing : CommRing (PolynomialCoordinateRing K) := by infer_instance
instance polynomialAlgebra : Algebra K (PolynomialCoordinateRing K) :=
  tensorObjectLeftAlgebra IntegerRing K LinearPolynomial

def polynomialBaseChangeEquiv :
    PolynomialCoordinateRing K ≃ₐ[K] MvPolynomial (Fin 3 × Fin 3) K :=
  MvPolynomial.algebraTensorAlgEquiv IntegerRing K

instance polynomialBaseChange_domain :
    IsDomain (PolynomialCoordinateRing K) :=
  MulEquiv.isDomain (MvPolynomial (Fin 3 × Fin 3) K)
    (polynomialBaseChangeEquiv K).toMulEquiv

def tensorDeterminant : PolynomialCoordinateRing K :=
  tensorRightElement IntegerRing.{u} K LinearPolynomial.{u} (generalLinearDeterminant.{u} 3)

theorem tensor_determinant_ne_zero : tensorDeterminant K ≠ 0 := by
  let f : LinearPolynomial.{u} →ₐ[IntegerRing.{u}] K :=
    MvPolynomial.aeval (fun ij : Fin 3 × Fin 3 => if ij.1 = ij.2 then 1 else 0)
  have hm : (Matrix.mvPolynomialX (Fin 3) (Fin 3) IntegerRing).map f = 1 := by
    ext i j
    simp [f, Matrix.mvPolynomialX, Matrix.one_apply]
  have hf : f (generalLinearDeterminant 3) = 1 := by
    change f (Matrix.mvPolynomialX (Fin 3) (Fin 3) IntegerRing).det = 1
    exact (RingHom.map_det f.toRingHom _).trans
      ((congrArg Matrix.det hm).trans (Matrix.det_one : (1 : Matrix (Fin 3) (Fin 3) K).det = 1))
  have hd : tensorEvaluation IntegerRing K LinearPolynomial f (tensorDeterminant K) = 1 := by
    rw [tensorDeterminant, tensorEvaluation_rightElement]
    exact hf
  intro hz
  have hc := congrArg (tensorEvaluation IntegerRing K LinearPolynomial f) hz
  rw [hd, map_zero] at hc
  exact one_ne_zero hc

abbrev LinearCoordinateRing : Type u :=
  tensorObject IntegerRing.{u} K (generalLinearCoordinateRing.{u} 3)

instance linearCommRing : CommRing (LinearCoordinateRing K) := by infer_instance
instance linearAlgebra : Algebra K (LinearCoordinateRing K) :=
  tensorObjectLeftAlgebra IntegerRing K (generalLinearCoordinateRing 3)

instance linearCoordinateRing_domain : IsDomain (LinearCoordinateRing K) := by
  let e : LinearCoordinateRing K ≃ₐ[K] Localization.Away (tensorDeterminant K) :=
    IsLocalization.Away.tensorProductEquivTMulRight IntegerRing.{u} K
      (generalLinearDeterminant.{u} 3) (generalLinearCoordinateRing.{u} 3)
  letI : IsDomain (Localization.Away (tensorDeterminant K)) :=
    Localization.Away.isDomain (tensor_determinant_ne_zero K)
  exact MulEquiv.isDomain _ e.toMulEquiv

abbrev ChartCoordinateRing : Type u :=
  tensorObject IntegerRing.{u} K Sp6GaussCellCoordinates.CoordinateRing.{u}

instance chartCommRing : CommRing (ChartCoordinateRing K) := by infer_instance
instance chartAlgebra : Algebra K (ChartCoordinateRing K) :=
  tensorObjectLeftAlgebra IntegerRing K Sp6GaussCellCoordinates.CoordinateRing

def chartBaseChangeEquiv :
    ChartCoordinateRing K ≃ₐ[K]
      MvPolynomial Sp6GaussCellCoordinates.ExtraIndex.{u} (LinearCoordinateRing K) :=
  MvPolynomial.rTensorAlgEquiv

instance chartCoordinateRing_domain : IsDomain (ChartCoordinateRing K) :=
  MulEquiv.isDomain
    (MvPolynomial Sp6GaussCellCoordinates.ExtraIndex (LinearCoordinateRing K))
    (chartBaseChangeEquiv K).toMulEquiv

instance chartBaseChange_integral : IsIntegral (Spec (.of (ChartCoordinateRing K))) := by
  infer_instance

end M9Native.Sp6GaussChartDomain

